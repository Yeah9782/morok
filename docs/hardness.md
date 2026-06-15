# Morok — implementation specification: hardness-backed primitives

This document specifies three additions whose analysis resistance reduces to a
**named hardness assumption** or a **provable algebraic invariant**, rather than
to instruction volume:

1. **T-function single-cycle state generator** (`core/TFunction.hpp`) — a
   provably full-period nonlinear dispatcher-state generator that replaces the
   logistic map in control-flow flattening.
2. **Multivariate-quadratic (MQ) input gate** (`core/MqGf2.hpp`) — a degree-2
   GF(2) gate that is cheap forward and MQ-hard to invert, hardening genuinely
   input-derived branches against symbolic input-finding.
3. **Shamir (k,n) threshold sharing bound to control flow**
   (`core/ShamirGf256.hpp`) — threshold reconstruction of a high-value value
   that is information-theoretically unrecoverable from sub-quorum coverage.

The three pure cores are already implemented and exhaustively/property-testable
with zero LLVM dependency, per the project's "prove the math in `core`, emit the
matching IR in the pass" methodology. This document records the *plumbing* each
needs in the `ir`/`passes`/`config`/`pipeline` layers — it is the porting
cheat-sheet, in the same spirit as `algorithms.md`.

All integer identities hold in `Z/2ⁿ` (two's-complement wraparound); all field
arithmetic is in `GF(2⁸)` under the AES reduction polynomial `0x11B`, matching
`core/Galois8.hpp`.

---

## 0. Conventions these specs assume

Recapped so the per-pass sections are unambiguous; all are already established
in the tree.

- **Pass shape.** Each transform is a free function
  `bool <name>Function(Function&, const <Name>Params&, ir::IRRandom&)` (or
  `<name>Module(Module&, …)` for module passes) returning whether it changed
  the IR, plus a thin New-PM wrapper `class <Name>Pass : PassInfoMixin<…>` that
  owns a seeded `core::Xoshiro256pp engine_` and exposes `-passes=morok-<name>`.
  The scheduler calls the free function directly with a `Params` populated from
  the resolved config.
- **Randomness.** One shared `core::Xoshiro256pp`, seeded once per run
  (`config_.seed != 0 ? fromSeed(seed) : makeSeededEngine()`), wrapped in
  `ir::IRRandom` (`next()`, `range(bound)`, `chance(percent)`, `constInt(ty)`).
  Every randomized choice draws from this engine, so a fixed `-morok-seed`
  reproduces the build and distinct seeds yield per-build polymorphism for free.
- **Opt-in/out.** `ir::shouldObfuscate(F, "<attr>", eff.<pass>.enabled.value_or(default))`
  gates every per-function pass; an `annotate("<attr>")` / `annotate("no<attr>")`
  on the source function overrides the default.
- **Generated-symbol convention.** Every global/function the passes synthesize
  is named `morok.*`; the per-function scheduler loop skips
  `F.getName().starts_with("morok.")`, and global-eligibility checks skip
  `morok.`/`llvm.` names. New globals follow `morok.<pass>.<role>.*`.
- **Config.** Each pass owns a struct of `Opt<T>` fields in
  `config::PassConfig`; "unset" means "use the pass default". `config::resolve`
  merges preset → TOML file → ordered policy → annotation, then the scheduler
  reads `eff.<pass>.<field>.value_or(<default>)`.
- **Test layers.** `core` exhaustive/property (no LLVM); `ir`/`passes`
  LLVM-linked validity (`verifyModule` + "the pass fired"); whole-stack `e2e`
  differential (obfuscated output byte-identical to clean across
  `low`/`mid`/`high` × seeds).

---

## 1. T-function single-cycle state generator

### 1.1 Motivation

`ChaosStateMachine` drives the flattening dispatcher with the Q16 logistic map.
`core/LogisticMap.hpp` documents the problem honestly: the pure `step` orbit
"cycles after a few hundred states — by design", so the sequence builder must
add an **impure anti-stuck XOR perturbation** to collect enough distinct
dispatcher states. That perturbation is a wart: it is the one place in the
flattening family where the state sequence is not a clean iterated map, and it
exists only to paper over the logistic map's short period.

The Klimov–Shamir quadratic T-function `step(x) = x + (x²|C) mod 2ⁿ` is a
**single cycle of full period 2ⁿ** exactly when `C` is odd and `C ≡ 5 or 7
(mod 8)` (verified exhaustively for `n ∈ {4,8,12,16}`; the criterion is
bit-local, so it lifts to 64). Consequences:

- The first `min(numBlocks, 2ⁿ)` iterates are **guaranteed distinct** — no
  anti-stuck hack, no impurity. The generator becomes a clean iterated map again.
- The recurrence mixes `+`, `*`, `|`: it is **genuinely nonlinear**, unlike the
  affine `x + c` that a linear single-cycle counter would emit and that MBA
  normalization / induction-variable analysis sees straight through.
- It composes with the existing data-entanglement: a deflattener that wants the
  "state is dead w.r.t. data" shortcut still cannot, and now also cannot model
  the transition as an affine IV.

This is a strict upgrade of an existing pass, not a new attack surface.

### 1.2 Architecture

`core::tfunc` is already shipped (`step`, `inverse`, `advance`, `correction`,
`isSingleCycleConstant`, `kDefaultC`). It mirrors the `core::chaos` surface
exactly, including a `correction(i, j)` whose XOR telescopes a logical
transition to its target id — so it is a **drop-in generator** for the existing
`ir::flattenControlFlow` engine. No new module-global state, no new scheduler
slot: the T-function is selected *within* the existing "exactly one flattening
layer per function" cascade.

The integration point is `chaosStateMachineFunction`, which today closes over a
`NextStateFn` lambda calling a local `emitStep` (logistic) plus
`core::chaos::correction`. We parameterize that on a generator selector.

### 1.3 Core API

No additions. The pass consumes:

```cpp
namespace morok::core::tfunc {
  constexpr bool     isSingleCycleConstant(uint64_t C) noexcept;   // C%8 ∈ {5,7}
  constexpr uint64_t step      (uint64_t x, unsigned bits, uint64_t C = 5);
  constexpr uint64_t correction(uint64_t encodedI, uint64_t idJ,
                                unsigned bits, uint64_t C = 5);
  // inverse(), advance() available for tests/completeness; the pass uses
  // step()+correction() only, exactly like the chaos generator.
}
```

### 1.4 Pass specification

**Generator selector.** Extend `CsmConfig` and thread the choice into the free
function:

```cpp
enum class StateGenerator { Logistic, TFunction };

struct CsmParams {                 // populated by the scheduler from CsmConfig
  StateGenerator generator = StateGenerator::Logistic;
  uint64_t       tf_const  = core::tfunc::kDefaultC;  // validated single-cycle
  uint32_t       warmup    = core::chaos::kDefaultWarmup;
  bool           nested    = false;
};

bool chaosStateMachineFunction(Function&, const CsmParams&, ir::IRRandom&);
```

**IR emission.** Add a sibling of the existing `emitStep`, computing the
T-function in `i32` and reproducing `core::tfunc::step(x, 32, C)` bit-for-bit so
the compile-time corrections telescope:

```text
xc      = x & 0xFFFFFFFF                 ; i32 domain == flattener state width
sq      = xc * xc                        ; wrapping i32
orC     = sq | C                         ; C is the validated constant
next    = xc + orC                       ; wrapping i32  == tfunc::step(xc,32,C)
```

The transition lambda is otherwise identical to the chaos generator: select the
per-edge correction constant (`core::tfunc::correction(currentId, targetId, 32,
C)`) over the `SuccessorIds` arms, then `return CreateXor(emitStepTF(B, cur),
corr)`. Because `emitStepTF` matches `core::tfunc::step` and `correction` is the
matching compile-time constant, `next == targetId` exactly.

**State width.** The flattener state variable is `i32`. At `n = 32` the
single-cycle constant criterion is unchanged (`C ≡ 5 or 7 mod 8`); default
`C = 5`. The orbit period is `2³²`, vastly exceeding any real block count, so
distinctness of the first `numBlocks` states is guaranteed without warm-up
(`warmup` is retained only for sequence-diversity parity with the chaos path and
may be 0).

**Per-build diversity.** Draw `C` per function from the valid residue class:
`C = (rng.next() & ~7u) | (rng.chance(50) ? 5u : 7u)`, asserted by
`core::tfunc::isSingleCycleConstant`. Do **not** compose two T-functions to
"increase nonlinearity": single-cycle permutations are *not* closed under
composition, and an affine outer wrap `a·x+b` (a odd) preserves bijectivity but
not necessarily the single cycle. One T-function with a per-build `C` is the
specified construction.

**Eligibility / idempotency / skips.** Identical to the chaos generator
(delegated to `flattenControlFlow`): ≥2 blocks, no EH/indirect terminators;
`shouldObfuscate(F, "csm", …)`; generated `morok.*` functions skipped by the
scheduler loop. A standalone `-passes=morok-tfa` wrapper may expose
`chaosStateMachineFunction` with `generator = TFunction` for targeted use.

### 1.5 Config schema

| Field (`CsmConfig`) | Type | Default | Notes |
|---|---|---|---|
| `enabled` | `Opt<bool>` | off | gate (`csm` attr) |
| `generator` | `Opt<enum>` | `logistic` | `logistic` \| `tfunction` |
| `tf_const` | `Opt<u64>` | `5` | rejected at resolve time unless `isSingleCycleConstant`; `0`/unset ⇒ per-build random valid C |
| `nested_dispatch` | `Opt<bool>` | off | existing |
| `warmup` | `Opt<u32>` | `64` | unused for `tfunction` (period ≫ blocks) |

TOML: `[passes.csm] generator = "tfunction"`. Validation lives in the resolver
(reject out-of-class constants with a diagnostic, like the existing
`share_count`/`width` clamps).

### 1.6 Scheduler placement

No new line. Within the existing one-flattening-layer cascade the precedence is
`NonInvertibleState → DataEntangledFlattening → ChaosStateMachine(generator) →
plain Flattening`; selecting `generator = tfunction` changes only *how* the CSM
slot computes the next state. `StateOpaquePredicates` / `InterproceduralFsm`
continue to compose on top because the dispatcher skeleton and `fla.state`
alloca are unchanged.

### 1.7 Test plan

- **core (`tests/unit/core/test_tfunction.cpp`).** Exhaustive single-cycle for
  `n ∈ {4,8,12,16}` over every starting point and every `C` in the candidate
  set — assert exactly the residue class `{C%8 ∈ {5,7}}` yields a full `2ⁿ`
  orbit. Exhaustive `inverse(step(x))==x` for all `2¹⁶` at `n=16`; random
  spot-check at `n=64`. `isSingleCycleConstant` truth table on `0..255`.
  Regression: the `n=64, C=5` reference vector in the header.
- **passes (`tests/ir/test_passes.cpp`).** With `generator=tfunction`, the pass
  verifies (`verifyModule`) and fires on a ≥2-block function; the emitted step
  block contains the `mul`/`or`/`add` shape (no logistic `lshr 30`). A small
  driver run confirms a flattened function still reaches every original block.
- **e2e (`tests/e2e`).** Add a `mid`/`high` variant with
  `csm.generator=tfunction`; the differential harness must reproduce reference
  output byte-for-byte across seeds (this is the semantics-preservation proof).

### 1.8 Weaknesses / guardrails

The `x+(x²|C)` family is *recognizable*: a deobfuscator can model the recurrence
symbolically. What it cannot do is slice the state out as a dead affine IV or
shortcut the orbit; the win is the removal of the impure anti-stuck path, plus
nonlinear state that strengthens the existing entanglement. Keep the state at
`i32`; do not compose generators; vary `C` per build for cross-binary diversity.

---

## 2. Multivariate-quadratic (MQ) input gate

### 2.1 Motivation

`PathExplosion` and `TraceKeying` raise the *cost* of symbolic exploration; they
are not backed by a hardness assumption. The MQ gate adds one that is: deciding
whether a system of multivariate quadratic equations over GF(2) has a common
root is NP-complete, and *random dense* systems are precisely the regime where
generic SAT and Gröbner-basis methods stall — the hardness underpinning
UOV/Rainbow signatures.

The asymmetry is the point. A planted quadratic system is trivial to
**evaluate** (a few AND/XOR per equation) but, at adequate width, intractable to
**invert** (find the satisfying assignment). Against a coverage-driven symbolic
engine asking "what input reaches this block?", the path constraint *is* an MQ
system. Against a keygen-style attacker forging an accepting input, forgery *is*
MQ. And unlike a cryptographic-hash gate — which is also SMT-hard but bloats both
the binary and the emitted SMT formula — a degree-2 system keeps both small.

### 2.2 Architecture

`core::mq` is shipped: `QuadForm`, `triIndex`, `evalForm`, `makePlantedForm`,
`Gate{opens}`, `makePlantedGate`. `makePlantedForm` re-bases each form's constant
so a chosen assignment `s` is a root, i.e. the gate **opens exactly at `s`**.

The pass is a new per-function member of the anti-DSE family. It harvests the
gate-input bits from genuinely input-derived values (the same harvesting
`DataEntangledFlattening`/`PathExplosion` already do over arguments and live
integers), emits the system as a private constant, evaluates `opens()` inline,
branches on it, and — crucially — folds the gate-failed signal into downstream
data exactly as `TraceKeying` folds its accumulator diff, so there is no
separable success/fail edge to patch.

Two honest operating modes, both relying on MQ-hardness against *symbolic*
adversaries (neither claims resistance to a single concrete trace):

- **Mode A — input validation.** The `m` bits are attacker-controlled input
  (serial, key, feature token). The gate opens iff input satisfies the system;
  a legitimate user supplies a valid input (a root exists — the planted `s` is
  one). Morok does not fabricate the input; it only emits the check. Forging an
  accepting input is MQ.
- **Mode B — anti-coverage on a derived predicate.** The `m` bits are derived
  from input by a known map `g`. Reaching the gated block under symbolic
  exploration requires solving `system ∘ g`; concrete runs that already drive
  `g(input)` to a root pass normally.

### 2.3 Pass specification

```cpp
struct MqParams {
  uint32_t probability = 20;   // per-eligible-branch coin
  uint32_t vars        = 64;   // m  (gate-input bit count)
  uint32_t eqs         = 64;   // keep ≈ vars; avoid over-defined systems
  uint32_t density     = 50;   // per-coefficient 1-probability, %
  uint32_t max_gates   = 4;    // per-function cap
  bool     fold_diff   = true; // TraceKeying-style poisoning of the bypass
};
bool mqGateFunction(Function&, const MqParams&, ir::IRRandom&);
```

**Selection.** Eligible sites are conditional branches whose condition is
(transitively) input-derived — detected by a shallow backward walk to function
arguments / loaded inputs, reusing the liveness harvest already used by the
entanglement passes. Cap by `max_gates` after a per-build shuffle; skip EH pads,
entry setup, and `morok.*` blocks.

**Bit harvesting.** Build the `m`-bit gate input from harvested `iN` values:
for each contributing value `v`, `bit_k = trunc i1 (lshr v, p_k)`; pack into the
`Gate`'s assignment order. Where fewer than `m` independent input bits are
available, top up from additional live values; the planted `s` is fixed to match
whatever the legitimate path produces (Mode A: a valid input's bits; Mode B:
`g(input)` on the intended branch).

**System emission.** At build time the coefficients are known, so emit **only
the nonzero terms** (the dense `QuadForm` is generated then pruned to its set
bits): each form is `XOR` of the selected `AND`-pairs `(b_i & b_j)` and linear
`b_i`, plus the constant; the gate is the `AND` of `form == 0` over all `eqs`.
Store the packed coefficient matrix as a private constant `morok.mq.sys.*`
(documentation/forensics only; the live check is the unrolled term tree). The
gate i1 replaces the original condition; the planted assignment guarantees the
intended edge at runtime.

**Bypass poisoning (`fold_diff`).** Compute `fail = zext(gate_failed)` and fold
a width-matched `fail * K` into the block's outgoing data/return exactly as
`TraceKeying` does (XOR into branch/switch conditions, XOR into integer
returns). On the valid path `fail == 0`; an attacker who forces the branch past
the gate still corrupts routing/output — so the gate cannot be NOP'd, only
solved.

### 2.4 Config schema

| Field (`MqConfig`) | Default | Notes |
|---|---|---|
| `enabled` | off | gate (`mq` attr) |
| `probability` | 20 | per input-derived branch |
| `vars` | 64 | `< ~32` is solvable instantly; specify ≥ 64 for margin |
| `eqs` | 64 | keep ≈ `vars`; over-defined systems can be easier |
| `density` | 50 | coefficient fill % |
| `max_gates` | 4 | per-function |
| `fold_diff` | true | bypass poisoning |

### 2.5 Scheduler placement

Insert **after `PathExplosion`, before `TraceKeying` and `Dispatcherless`**, in
the anti-DSE band:

```text
… → PathExplosion → MqGate → TraceKeying → Dispatcherless → SelfChecksum → …
```

This lets `TraceKeying`/`Dispatcherless` further hide the gate's branch, and
keeps the gate's `select`/`icmp` tree from being amplified by the value-level
passes that run earlier.

### 2.6 Test plan

- **core (`test_mq_gf2.cpp`).** For random `(m, eqs, density)` with a planted
  `s`: assert `gate.opens(s)` and that a large random sample of `x ≠ s` does not
  open (statistical — false-open probability `≈ 2^{-eqs}`). `triIndex` is a
  bijection onto `[0, m(m+1)/2)`; `evalForm` matches a brute-force reference on
  small `m`.
- **passes.** The pass verifies and fires; the emitted gate tree contains only
  `and`/`xor`/`icmp eq`/`select`, no division/loads of the system in the hot
  path; `max_gates` respected.
- **e2e.** Differential build where the fixtures supply the planted/valid input
  ⇒ byte-identical output. A **separate, non-differential** targeted test feeds
  a non-satisfying input and asserts the `fold_diff` corruption path diverges
  (this test is excluded from the byte-identical suite by construction).

### 2.7 Weaknesses / guardrails

Hardness needs adequate width: `m ≳ 64` and `eqs ≈ m` (small or heavily
over-defined systems solve quickly). Code size grows ~`m²` in pruned terms; cap
`max_gates`. MQ resists *symbolic input-finding*, **not** concrete execution — a
single observed valid run reveals the accepting input. Therefore restrict the
pass to genuinely input-derived conditions (a constant-derived condition gains
nothing) and lean on `fold_diff` for tamper-resistance of the bypass.

---

## 3. Shamir (k,n) threshold sharing bound to control flow

### 3.1 Motivation

`ConstantEncryption`/`XorShare` split a literal into shares **all** of which are
required (additive sharing). The threshold generalization, built on the
`GF(2⁸)` field already proven in `Galois8.hpp`, makes a value the constant term
of a random degree-`(k-1)` polynomial; any `k` of `n` evaluation shares
reconstruct it by Lagrange interpolation, and **any `k-1` shares are
information-theoretically independent of it**.

The obfuscation move is to bind the shares to control flow: deposit the `n`
shares at `n` distinct program points and reconstruct only after a quorum of `k`
has executed. A high-value value (a constant, a jump-table index, a key) then
materializes only along paths reaching quorum, and any partial backward slice or
sub-quorum path yields **provably zero information** — a strictly stronger claim
than the cost-based passes.

### 3.2 Architecture

`core::shamir` is shipped: `split(secret,k,n)`, `reconstruct(shares)` (Lagrange
at 0, with characteristic-2 simplification: `-x ≡ x`, `a-b ≡ a^b`), `evalPoly`.
The pass is a new per-function transform placed just before `ConstantEncryption`
(so the emitted share globals are themselves constant-encrypted) and after
`SelfChecksumConstants`. It reuses the `getOrCreateGf8Mul` → `morok.gf8mul`
idiom from `StringEncryption`.

Two placement strategies, differing in their correctness obligation:

- **`dominator` (default, provably correct).** Choose `k` deposit blocks that
  **all dominate** the use site, so every path reaching the use has populated
  all `k` shares; the abscissa set is therefore fixed and known at build time.
  Then the Lagrange basis coefficients `L_j(0) = ∏_{m≠j} x_m·inv(x_j ⊕ x_m)` are
  **compile-time constants in GF(2⁸)**, and reconstruction collapses to
  `secret = XOR_j gf8mul(share_j, L_j)` — `k` loads, `k` constant-multiplies,
  and a XOR-fold. No field inverse is emitted in IR; only `morok.gf8mul` is
  needed. This is a build-time specialization of `shamir::reconstruct` for the
  fixed abscissae.
- **`distributed` (advanced).** Shares deposited across genuinely distinct paths
  (any `k` of `n`). Requires a runtime populated-share selection and Lagrange
  over the *actual* abscissae, hence a baked public inverse table
  `morok.shamir.ginv` (256 bytes, filled at build with `core::gf8::inv`; field
  structure, not secret) plus a small reconstruction loop. The pass must prove
  (or conservatively guarantee by construction) that ≥`k` shares are populated
  on every path reaching the use.

### 3.3 Pass specification

```cpp
enum class SharePlacement { Dominator, Distributed };

struct ShamirParams {
  uint32_t       probability = 30;     // per eligible value
  uint32_t       threshold   = 3;      // k  (≥2)
  uint32_t       shares      = 5;      // n  (≥k, ≤255)
  uint32_t       max_secrets = 8;      // per-function cap
  SharePlacement placement   = SharePlacement::Dominator;
};
bool shamirShareFunction(Function&, const ShamirParams&, ir::IRRandom&);
```

**Target selection.** Eligible values are high-value `i8…i64` constants
(operands of selected instructions), jump-table indices, or keys introduced by
earlier passes. Truncate wider secrets into per-byte Shamir shares (one
polynomial per byte) and recombine; `i8` is the natural unit. Cap by
`max_secrets`; skip `morok.*`.

**Share globals.** `split(secretByte, k, n, rng)` → emit each share value into a
private mutable global `morok.shamir.share.*` (so a later pass / the loader can
relocate them; they are not the secret). Abscissae are `1..n`.

**Deposit + quorum.**
- *Dominator:* select `k` blocks dominating the use; in each, a (volatile) store
  publishes its share into a per-secret cell `morok.shamir.cell.*` (or simply
  reference the share global directly, since domination guarantees liveness).
  Reconstruct at the use site with the constant-folded form above.
- *Distributed:* in each of the `n` deposit blocks, store `(abscissa_i,
  share_i)` into `morok.shamir.cell.*` and set a populated-bit; at the use site,
  gather the first `k` populated entries and run the `morok.gf8mul` +
  `morok.shamir.ginv` Lagrange loop. The pass emits a build-time assertion that
  the chosen deposit blocks guarantee ≥`k` on all paths to the use.

**Reconstruction IR (dominator).** With abscissae `{1,2,3}` for `k=3`, the basis
`L_j(0)` are three `GF(2⁸)` constants computed at build time; emit
`r = gf8mul(s1,L1) ^ gf8mul(s2,L2) ^ gf8mul(s3,L3)` where `s_*` are the loaded
share bytes. By Lagrange this equals the secret exactly, proven by the same
field round-trip the core test exercises.

### 3.4 Config schema

| Field (`ShamirShareConfig`) | Default | Notes |
|---|---|---|
| `enabled` | off | gate (`shamir` attr) |
| `probability` | 30 | per eligible value |
| `threshold` (`k`) | 3 | clamp ≥2 |
| `shares` (`n`) | 5 | clamp `[k,255]` |
| `max_secrets` | 8 | per-function |
| `placement` | `dominator` | `dominator` \| `distributed` |

### 3.5 Scheduler placement

```text
… → SelfChecksum → ShamirShare → ConstEnc → IndirectBranch → …
```

Before `ConstEnc` so the share globals get XOR-share-encrypted (defense in depth,
mirroring the `SelfChecksum`→`ConstEnc` ordering rationale); after `SelfChecksum`
so integrity fusion targets the original constants, not share reconstructions.

### 3.6 Test plan

- **core (`test_shamir_gf256.cpp`).** Exhaustive: all 256 secrets, `k=3,n=5`,
  every 3-subset reconstructs the secret. Property: random `(k,n,secret,subset)`
  round-trips. Regression: the `secret=0x42,k=3,n=5,coeffs={0x42,0x1D,0x8C}`
  share vector and its reconstruction in the header.
- **passes.** The pass verifies and fires; dominator mode emits exactly `k`
  loads + `k` `gf8mul` + XOR (no inverse, no loop); `max_secrets` respected;
  share globals are private and `morok.shamir.*`.
- **e2e.** This is the correctness proof: with shares deposited and reconstructed
  on the real path, output is byte-identical across `low`/`mid`/`high` × seeds.
  The differential harness is exactly the right gate — a reconstruction bug
  surfaces immediately as divergent output.

### 3.7 Weaknesses / guardrails

The value is reconstructed in a register **at runtime**, so a dynamic attacker
at the reconstruction point sees plaintext — Shamir hides the value from *static*
and *sub-quorum* analysis, not from a breakpoint at the use site. The
`distributed` mode's information-theoretic story only holds if the `n` deposits
lie on genuinely distinct control paths; the `dominator` default trades that for
provable correctness (statically it reads as "value computed from `k` constants",
but each share is independently encrypted by `ConstEnc` and no single share
reveals anything). Prefer `dominator` unless a specific path structure justifies
`distributed`.

---

## 4. Cross-cutting integration

### 4.1 Preset values

Suggested entries for the preset tables (`config/Preset.cpp`), scaling with the
existing convention (off in `low`, modest in `mid`, full in `high`):

| Knob | low | mid | high |
|---|---|---|---|
| `csm.generator` | — | `tfunction` | `tfunction` |
| `csm.tf_const` | — | random valid | random valid |
| `mq.enabled` / `probability` | off | off | on / 15 |
| `mq.vars` / `eqs` | — | — | 64 / 64 |
| `shamir.enabled` / `probability` | off | on / 15 | on / 30 |
| `shamir.threshold` / `shares` | — | 3 / 5 | 3 / 5 |

MQ is `high`-only by default: it is the heaviest (code size, and it only helps on
input-derived branches). The T-function is free relative to the logistic map and
strictly better, so `mid`+ default to it.

### 4.2 Annotations

New per-function attrs honored by `shouldObfuscate`: `tfa` (standalone
T-function flattening), `mq`, `shamir`, with their `no*` opposites. The existing
`csm` attr continues to gate the flattening slot regardless of generator.

### 4.3 Registration & build checklist

- `core/`: header-only, already present; add only the three
  `tests/unit/core/test_*.cpp` and their `CMakeLists.txt` entries.
- `passes/`: add `MqGate.cpp`, `ShamirShare.cpp` (and headers) to
  `src/passes/CMakeLists.txt`; the T-function modifies `ChaosStateMachine.cpp`
  (add `emitStepTF`, `CsmParams`) and may add a thin `morok-tfa` wrapper.
- `config/`: add `MqConfig`, `ShamirShareConfig`, and `CsmConfig.generator`/
  `.tf_const` to `PassConfig.hpp`; extend the TOML loader, resolver validation
  (reject non-single-cycle `tf_const`, clamp `k`/`n`/`vars`), and preset tables.
- `pipeline/`: add the two scheduler blocks at the placements in §2.5/§3.5,
  reading `eff.mq.*` / `eff.shamir.*` via `value_or`; pass `CsmParams.generator`
  into the existing CSM call.
- `Plugin.cpp`: register `-passes=morok-mq`, `-passes=morok-shamir`,
  `-passes=morok-tfa`.
- `docs/algorithms.md`: add one entry per primitive in the existing format.

### 4.4 Polymorphism & determinism

All three draw exclusively from the shared `IRRandom` engine: the system
coefficients, the planted/abscissa choices, the deposit-block selection, and the
per-build `C` are all seeded, so `-morok-seed` reproduces the build and distinct
seeds produce structurally distinct binaries (different MQ systems, different
share polynomials, different `C`), defeating cross-binary diffing for free.

---

## 5. Honest ceiling

Stated plainly so each piece is aimed correctly. The T-function, Shamir, and MQ
are, respectively, a **correctness upgrade** (full-period nonlinear state with no
impure hack), an **information-theoretic** guarantee against *sub-quorum / static
partial* analysis, and a **named-hardness** guarantee against *symbolic
input-finding*. None of them resists a full concrete trace sitting at the
generator step, the reconstruction point, or the gate evaluation — a dynamic
attacker there observes concrete state. The durable, hard-to-argue-away wins are
exactly those three framed claims; layering them with the existing entanglement,
trace-keying, and constant-encryption passes is what raises the cost of getting
to those observation points. Do not document any of these as "undeobfuscatable";
document them as what they are.
