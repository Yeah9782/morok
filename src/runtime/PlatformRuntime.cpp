// SPDX-License-Identifier: MIT
//
// Morok — modular LLVM IR obfuscator.
//
// Centralized platform primitive emission.  Passes call through this layer so
// syscall numbers, ABI constraints, direct/fallback policy, and import surface
// decisions are audited in one place.

#include "morok/runtime/PlatformRuntime.hpp"

#include "llvm/IR/Constants.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"

#include <array>
#include <vector>

using namespace llvm;

namespace morok::runtime {

IntegerType *platformWordTy(Module &M) {
    unsigned Bits = M.getDataLayout().getPointerSizeInBits(0);
    if (Bits == 0)
        Bits = 64;
    return IntegerType::get(M.getContext(), Bits);
}

Value *toSyscallArg(IRBuilderBase &B, Value *V) {
    auto *IP = platformWordTy(*B.GetInsertBlock()->getModule());
    if (V->getType()->isPointerTy())
        return B.CreatePtrToInt(V, IP);
    if (V->getType()->isIntegerTy())
        return B.CreateSExtOrTrunc(V, IP);
    return ConstantInt::get(IP, 0);
}

FunctionCallee ptraceDecl(Module &M) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *Ptr = PointerType::getUnqual(Ctx);
    return M.getOrInsertFunction(
        "ptrace", FunctionType::get(I32, {I32, I32, Ptr, I32}, false));
}

FunctionCallee syscallDecl(Module &M) {
    auto *IP = platformWordTy(M);
    return M.getOrInsertFunction("syscall", FunctionType::get(IP, {IP}, true));
}

FunctionCallee getpidDecl(Module &M) {
    return M.getOrInsertFunction(
        "getpid", FunctionType::get(Type::getInt32Ty(M.getContext()), false));
}

FunctionCallee getppidDecl(Module &M) {
    return M.getOrInsertFunction(
        "getppid", FunctionType::get(Type::getInt32Ty(M.getContext()), false));
}

FunctionCallee openDecl(Module &M) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *Ptr = PointerType::getUnqual(Ctx);
    return M.getOrInsertFunction("open",
                                 FunctionType::get(I32, {Ptr, I32}, true));
}

FunctionCallee readDecl(Module &M) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *Ptr = PointerType::getUnqual(Ctx);
    auto *IP = platformWordTy(M);
    return M.getOrInsertFunction("read",
                                 FunctionType::get(IP, {I32, Ptr, IP}, false));
}

FunctionCallee closeDecl(Module &M) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    return M.getOrInsertFunction("close", FunctionType::get(I32, {I32}, false));
}

FunctionCallee readlinkDecl(Module &M) {
    LLVMContext &Ctx = M.getContext();
    auto *Ptr = PointerType::getUnqual(Ctx);
    auto *IP = platformWordTy(M);
    return M.getOrInsertFunction(
        "readlink", FunctionType::get(IP, {Ptr, Ptr, IP}, false));
}

FunctionCallee lseekDecl(Module &M) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *IP = platformWordTy(M);
    return M.getOrInsertFunction("lseek",
                                 FunctionType::get(IP, {I32, IP, I32}, false));
}

FunctionCallee mmapDecl(Module &M) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *Ptr = PointerType::getUnqual(Ctx);
    auto *IP = platformWordTy(M);
    return M.getOrInsertFunction(
        "mmap", FunctionType::get(Ptr, {Ptr, IP, I32, I32, I32, IP}, false));
}

FunctionCallee munmapDecl(Module &M) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *Ptr = PointerType::getUnqual(Ctx);
    auto *IP = platformWordTy(M);
    return M.getOrInsertFunction("munmap",
                                 FunctionType::get(I32, {Ptr, IP}, false));
}

FunctionCallee mprotectDecl(Module &M) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *Ptr = PointerType::getUnqual(Ctx);
    auto *IP = platformWordTy(M);
    return M.getOrInsertFunction(
        "mprotect", FunctionType::get(I32, {Ptr, IP, I32}, false));
}

bool useDirectLinuxSyscalls(const Triple &TT) {
    return TT.isOSLinux() && TT.getArch() == Triple::x86_64;
}

bool lookupLinuxCoreSyscalls(const Triple &TT, LinuxCoreSyscalls &Out) {
    switch (TT.getArch()) {
    case Triple::x86_64:
        Out.ptrace = 101;
        Out.prctl = 157;
        Out.openat = 257;
        Out.read = 0;
        Out.close = 3;
        return true;
    case Triple::aarch64:
        Out.ptrace = 117;
        Out.prctl = 167;
        Out.openat = 56;
        Out.read = 63;
        Out.close = 57;
        return true;
    default:
        return false;
    }
}

bool lookupLinuxCleanCopySyscalls(const Triple &TT,
                                  LinuxCleanCopySyscalls &Out) {
    switch (TT.getArch()) {
    case Triple::x86_64:
        Out.readlink = 89;
        Out.lseek = 8;
        Out.mmap = 9;
        Out.munmap = 11;
        return true;
    default:
        return false;
    }
}

Value *emitPtraceImport(IRBuilderBase &B, Module &M, int Request) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *Ptr = PointerType::getUnqual(Ctx);
    return B.CreateCall(ptraceDecl(M), {ConstantInt::getSigned(I32, Request),
                                        ConstantInt::get(I32, 0),
                                        ConstantPointerNull::get(Ptr),
                                        ConstantInt::get(I32, 0)});
}

Value *emitLinuxSyscall(IRBuilder<> &B, Module &M, const Triple &TT,
                        std::uint32_t Number,
                        std::initializer_list<Value *> Args,
                        const Twine &Name) {
    auto *IP = platformWordTy(M);
    std::array<Value *, 6> SysArgs = {
        ConstantInt::get(IP, 0), ConstantInt::get(IP, 0),
        ConstantInt::get(IP, 0), ConstantInt::get(IP, 0),
        ConstantInt::get(IP, 0), ConstantInt::get(IP, 0)};
    std::size_t I = 0;
    for (Value *Arg : Args) {
        if (I >= SysArgs.size())
            break;
        SysArgs[I++] = toSyscallArg(B, Arg);
    }

    if (useDirectLinuxSyscalls(TT)) {
        std::vector<Type *> Params(7, IP);
        auto *AsmTy = FunctionType::get(IP, Params, false);
        InlineAsm *Syscall = InlineAsm::get(
            AsmTy, "syscall",
            "={rax},{rax},{rdi},{rsi},{rdx},{r10},{r8},{r9},~{rcx},~{r11},"
            "~{memory},~{dirflag},~{fpsr},~{flags}",
            /*hasSideEffects=*/true);
        return B.CreateCall(AsmTy, Syscall,
                            {ConstantInt::get(IP, Number), SysArgs[0],
                             SysArgs[1], SysArgs[2], SysArgs[3], SysArgs[4],
                             SysArgs[5]},
                            Name);
    }

    return B.CreateCall(syscallDecl(M),
                        {ConstantInt::get(IP, Number), SysArgs[0], SysArgs[1],
                         SysArgs[2], SysArgs[3], SysArgs[4], SysArgs[5]},
                        Name + ".wrap");
}

Value *emitLinuxPtrace(IRBuilder<> &B, Module &M, const Triple &TT,
                       int Request) {
    LinuxCoreSyscalls Sys;
    if (!lookupLinuxCoreSyscalls(TT, Sys))
        return emitPtraceImport(B, M, Request);
    auto *I32 = Type::getInt32Ty(M.getContext());
    auto *IP = platformWordTy(M);
    auto *Ptr = PointerType::getUnqual(M.getContext());
    Value *Rc = emitLinuxSyscall(
        B, M, TT, Sys.ptrace,
        {ConstantInt::getSigned(IP, Request), ConstantInt::get(IP, 0),
         ConstantPointerNull::get(Ptr), ConstantInt::get(IP, 0)});
    return B.CreateTruncOrBitCast(Rc, I32);
}

Value *emitLinuxPrctl(IRBuilder<> &B, Module &M, const Triple &TT,
                      std::int64_t Option, std::int64_t A2, std::int64_t A3,
                      std::int64_t A4, std::int64_t A5) {
    LinuxCoreSyscalls Sys;
    if (!lookupLinuxCoreSyscalls(TT, Sys)) {
        auto *I32 = Type::getInt32Ty(M.getContext());
        auto *IP = platformWordTy(M);
        FunctionCallee Prctl = M.getOrInsertFunction(
            "prctl", FunctionType::get(I32, {I32, IP, IP, IP, IP}, false));
        auto Arg = [&](std::int64_t V) {
            return ConstantInt::getSigned(IP, V);
        };
        return B.CreateCall(Prctl, {ConstantInt::getSigned(I32, Option),
                                    Arg(A2), Arg(A3), Arg(A4), Arg(A5)});
    }

    auto *I32 = Type::getInt32Ty(M.getContext());
    auto *IP = platformWordTy(M);
    Value *Rc = emitLinuxSyscall(
        B, M, TT, Sys.prctl,
        {ConstantInt::getSigned(IP, Option), ConstantInt::getSigned(IP, A2),
         ConstantInt::getSigned(IP, A3), ConstantInt::getSigned(IP, A4),
         ConstantInt::getSigned(IP, A5)});
    return B.CreateTruncOrBitCast(Rc, I32);
}

bool useDirectDarwinSyscalls(const Triple &TT) {
    return TT.isOSDarwin() && TT.getArch() == Triple::x86_64;
}

static Value *emitArm64SvcInlineAsm(IRBuilder<> &B, Module &M, Value *Nr,
                                    const std::array<Value *, 6> &A,
                                    const Twine &Name) {
    auto *IP = platformWordTy(M);
    std::vector<Type *> Params(7, IP);
    auto *AsmTy = FunctionType::get(IP, Params, false);
    InlineAsm *Svc = InlineAsm::get(
        AsmTy, "svc #0x80",
        "={x0},{x16},0,{x1},{x2},{x3},{x4},{x5},~{memory},~{cc}",
        /*hasSideEffects=*/true);
    return B.CreateCall(AsmTy, Svc, {Nr, A[0], A[1], A[2], A[3], A[4], A[5]},
                        Name);
}

static Function *getOrCreateSvcFallback(Module &M) {
    if (auto *F = M.getFunction("morok.svc.fallback"))
        return F;
    LLVMContext &Ctx = M.getContext();
    auto *IP = platformWordTy(M);
    std::vector<Type *> Params(7, IP);
    auto *SysTy = FunctionType::get(IP, Params, false);
    Function *Fb = Function::Create(SysTy, GlobalValue::InternalLinkage,
                                    "morok.svc.fallback", &M);
    Fb->addFnAttr(Attribute::NoInline);
    BasicBlock *BB = BasicBlock::Create(Ctx, "entry", Fb);
    IRBuilder<> FB(BB);
    auto AI = Fb->arg_begin();
    Value *Nr = &*AI++;
    std::array<Value *, 6> A{};
    for (std::size_t K = 0; K < 6; ++K)
        A[K] = &*AI++;
    FB.CreateRet(emitArm64SvcInlineAsm(FB, M, Nr, A, "morok.darwin.svc"));
    return Fb;
}

Value *emitDarwinArm64Svc(IRBuilder<> &B, Module &M, std::uint32_t Number,
                          std::initializer_list<Value *> Args,
                          const Twine &Name) {
    auto *IP = platformWordTy(M);
    std::array<Value *, 6> A = {ConstantInt::get(IP, 0),
                                ConstantInt::get(IP, 0),
                                ConstantInt::get(IP, 0),
                                ConstantInt::get(IP, 0),
                                ConstantInt::get(IP, 0),
                                ConstantInt::get(IP, 0)};
    std::size_t I = 0;
    for (Value *Arg : Args)
        if (I < A.size())
            A[I++] = toSyscallArg(B, Arg);
    Function *Fallback = getOrCreateSvcFallback(M);
    return B.CreateCall(Fallback->getFunctionType(), Fallback,
                        {ConstantInt::get(IP, Number), A[0], A[1], A[2], A[3],
                         A[4], A[5]},
                        Name);
}

Value *emitDarwinSyscall(IRBuilder<> &B, Module &M, const Triple &TT,
                         std::uint32_t Number,
                         std::initializer_list<Value *> Args,
                         const Twine &Name) {
    auto *IP = platformWordTy(M);
    std::array<Value *, 6> SysArgs = {
        ConstantInt::get(IP, 0), ConstantInt::get(IP, 0),
        ConstantInt::get(IP, 0), ConstantInt::get(IP, 0),
        ConstantInt::get(IP, 0), ConstantInt::get(IP, 0)};
    std::size_t I = 0;
    for (Value *Arg : Args) {
        if (I >= SysArgs.size())
            break;
        SysArgs[I++] = toSyscallArg(B, Arg);
    }

    if (useDirectDarwinSyscalls(TT)) {
        std::vector<Type *> Params(7, IP);
        auto *AsmTy = FunctionType::get(IP, Params, false);
        InlineAsm *Syscall = InlineAsm::get(
            AsmTy, "syscall\nsbbq %r11, %r11\norq %r11, %rax",
            "={rax},{rax},{rdi},{rsi},{rdx},{r10},{r8},{r9},~{rcx},~{r11},"
            "~{memory},~{dirflag},~{fpsr},~{flags}",
            /*hasSideEffects=*/true);
        return B.CreateCall(AsmTy, Syscall,
                            {ConstantInt::get(IP, 0x02000000U | Number),
                             SysArgs[0], SysArgs[1], SysArgs[2], SysArgs[3],
                             SysArgs[4], SysArgs[5]},
                            Name);
    }

    return B.CreateCall(syscallDecl(M),
                        {ConstantInt::get(IP, Number), SysArgs[0], SysArgs[1],
                         SysArgs[2], SysArgs[3], SysArgs[4], SysArgs[5]},
                        Name + ".wrap");
}

Value *emitDarwinGetpid(IRBuilder<> &B, Module &M, const Triple &TT) {
    auto *I32 = Type::getInt32Ty(M.getContext());
    if (useDirectDarwinSyscalls(TT))
        return B.CreateTruncOrBitCast(emitDarwinSyscall(B, M, TT, 20, {}), I32);
    if (TT.getArch() == Triple::aarch64)
        return B.CreateTruncOrBitCast(emitDarwinArm64Svc(B, M, 20, {}), I32);
    return B.CreateCall(getpidDecl(M));
}

Value *emitDarwinPtrace(IRBuilder<> &B, Module &M, const Triple &TT,
                        std::int32_t Request) {
    auto *I32 = Type::getInt32Ty(M.getContext());
    auto *Ptr = PointerType::getUnqual(M.getContext());
    if (useDirectDarwinSyscalls(TT))
        return B.CreateTruncOrBitCast(
            emitDarwinSyscall(
                B, M, TT, 26,
                {ConstantInt::getSigned(I32, Request), ConstantInt::get(I32, 0),
                 ConstantPointerNull::get(Ptr), ConstantInt::get(I32, 0)}),
            I32);
    if (TT.getArch() == Triple::aarch64)
        return B.CreateTruncOrBitCast(
            emitDarwinArm64Svc(
                B, M, 26,
                {ConstantInt::getSigned(I32, Request), ConstantInt::get(I32, 0),
                 ConstantPointerNull::get(Ptr), ConstantInt::get(I32, 0)}),
            I32);
    return emitPtraceImport(B, M, Request);
}

Value *emitDarwinSysctl(IRBuilder<> &B, Module &M, const Triple &TT, Value *Mib,
                        Value *MibLen, Value *OldP, Value *OldLenP, Value *NewP,
                        Value *NewLen) {
    auto *I32 = Type::getInt32Ty(M.getContext());
    auto *IP = platformWordTy(M);
    auto *Ptr = PointerType::getUnqual(M.getContext());
    if (useDirectDarwinSyscalls(TT))
        return B.CreateTruncOrBitCast(
            emitDarwinSyscall(B, M, TT, 202,
                              {Mib, MibLen, OldP, OldLenP, NewP, NewLen}),
            I32);
    if (TT.getArch() == Triple::aarch64)
        return B.CreateTruncOrBitCast(
            emitDarwinArm64Svc(B, M, 202,
                               {Mib, MibLen, OldP, OldLenP, NewP, NewLen}),
            I32);
    FunctionCallee Sysctl = M.getOrInsertFunction(
        "sysctl", FunctionType::get(I32, {Ptr, I32, Ptr, Ptr, Ptr, IP}, false));
    return B.CreateCall(Sysctl,
                        {Mib, B.CreateTruncOrBitCast(MibLen, I32), OldP,
                         OldLenP, NewP, B.CreateZExtOrTrunc(NewLen, IP)});
}

Value *emitDarwinCsops(IRBuilder<> &B, Module &M, const Triple &TT, Value *Pid,
                       Value *Ops, Value *UserAddr, Value *UserSize) {
    auto *I32 = Type::getInt32Ty(M.getContext());
    auto *IP = platformWordTy(M);
    auto *Ptr = PointerType::getUnqual(M.getContext());
    if (useDirectDarwinSyscalls(TT))
        return B.CreateTruncOrBitCast(
            emitDarwinSyscall(B, M, TT, 169, {Pid, Ops, UserAddr, UserSize}),
            I32);
    if (TT.getArch() == Triple::aarch64)
        return B.CreateTruncOrBitCast(
            emitDarwinArm64Svc(B, M, 169, {Pid, Ops, UserAddr, UserSize}), I32);
    FunctionCallee Csops = M.getOrInsertFunction(
        "csops", FunctionType::get(I32, {I32, I32, Ptr, IP}, false));
    return B.CreateCall(Csops, {B.CreateTruncOrBitCast(Pid, I32),
                                B.CreateTruncOrBitCast(Ops, I32), UserAddr,
                                B.CreateZExtOrTrunc(UserSize, IP)});
}

Value *emitLinuxReadlink(IRBuilder<> &B, Module &M, const Triple &TT,
                         Value *Path, Value *Buf, Value *Size) {
    LinuxCleanCopySyscalls Sys;
    if (useDirectLinuxSyscalls(TT) && lookupLinuxCleanCopySyscalls(TT, Sys))
        return emitLinuxSyscall(B, M, TT, Sys.readlink, {Path, Buf, Size});
    return B.CreateCall(readlinkDecl(M), {Path, Buf, Size},
                        "morok.clean.readlink");
}

Value *emitLinuxLseek(IRBuilder<> &B, Module &M, const Triple &TT, Value *Fd,
                      std::int64_t Offset, std::int32_t Whence) {
    LinuxCleanCopySyscalls Sys;
    if (useDirectLinuxSyscalls(TT) && lookupLinuxCleanCopySyscalls(TT, Sys))
        return emitLinuxSyscall(
            B, M, TT, Sys.lseek,
            {Fd, ConstantInt::getSigned(platformWordTy(M), Offset),
             ConstantInt::getSigned(Type::getInt32Ty(M.getContext()), Whence)});
    return B.CreateCall(
        lseekDecl(M),
        {B.CreateTruncOrBitCast(Fd, Type::getInt32Ty(M.getContext())),
         ConstantInt::getSigned(platformWordTy(M), Offset),
         ConstantInt::getSigned(Type::getInt32Ty(M.getContext()), Whence)},
        "morok.clean.lseek");
}

Value *emitLinuxMmapAddr(IRBuilder<> &B, Module &M, const Triple &TT,
                         Value *Size, Value *Fd) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *IP = platformWordTy(M);
    auto *Ptr = PointerType::getUnqual(Ctx);
    constexpr std::uint32_t kProtRead = 1;
    constexpr std::uint32_t kMapPrivate = 2;

    LinuxCleanCopySyscalls Sys;
    if (useDirectLinuxSyscalls(TT) && lookupLinuxCleanCopySyscalls(TT, Sys))
        return emitLinuxSyscall(B, M, TT, Sys.mmap,
                                {ConstantPointerNull::get(Ptr), Size,
                                 ConstantInt::get(I32, kProtRead),
                                 ConstantInt::get(I32, kMapPrivate), Fd,
                                 ConstantInt::get(IP, 0)});

    Value *Mapped = B.CreateCall(
        mmapDecl(M),
        {ConstantPointerNull::get(Ptr), Size, ConstantInt::get(I32, kProtRead),
         ConstantInt::get(I32, kMapPrivate), B.CreateTruncOrBitCast(Fd, I32),
         ConstantInt::get(IP, 0)},
        "morok.clean.mmap");
    return B.CreatePtrToInt(Mapped, IP);
}

void emitLinuxMunmap(IRBuilder<> &B, Module &M, const Triple &TT, Value *Addr,
                     Value *Size) {
    LinuxCleanCopySyscalls Sys;
    if (useDirectLinuxSyscalls(TT) && lookupLinuxCleanCopySyscalls(TT, Sys)) {
        emitLinuxSyscall(B, M, TT, Sys.munmap, {Addr, Size});
        return;
    }
    B.CreateCall(
        munmapDecl(M),
        {B.CreateIntToPtr(Addr, PointerType::getUnqual(M.getContext())), Size});
}

Value *emitLinuxMprotect(IRBuilder<> &B, Module &M, const Triple &TT,
                         Value *Addr, Value *Size, Value *Prot) {
    std::uint32_t MprotectNr = 0;
    if (TT.getArch() == Triple::x86_64)
        MprotectNr = 10;
    if (useDirectLinuxSyscalls(TT) && MprotectNr != 0)
        return B.CreateTruncOrBitCast(
            emitLinuxSyscall(B, M, TT, MprotectNr, {Addr, Size, Prot}),
            Type::getInt32Ty(M.getContext()));

    auto *I32 = Type::getInt32Ty(M.getContext());
    auto *Ptr = PointerType::getUnqual(M.getContext());
    return B.CreateCall(mprotectDecl(M), {B.CreateIntToPtr(Addr, Ptr), Size,
                                          B.CreateTruncOrBitCast(Prot, I32)});
}

void emitLinuxClose(IRBuilder<> &B, Module &M, const Triple &TT, Value *Fd) {
    LinuxCoreSyscalls Sys;
    if (lookupLinuxCoreSyscalls(TT, Sys)) {
        emitLinuxSyscall(B, M, TT, Sys.close, {Fd});
        return;
    }
    B.CreateCall(closeDecl(M), {B.CreateTruncOrBitCast(
                                   Fd, Type::getInt32Ty(M.getContext()))});
}

Value *emitDarwinOpen(IRBuilder<> &B, Module &M, const Triple &TT, Value *Path,
                      std::int32_t Flags, std::int32_t Mode) {
    auto *I32 = Type::getInt32Ty(M.getContext());
    if (useDirectDarwinSyscalls(TT))
        return B.CreateTruncOrBitCast(
            emitDarwinSyscall(B, M, TT, 5,
                              {Path, ConstantInt::getSigned(I32, Flags),
                               ConstantInt::getSigned(I32, Mode)}),
            I32);
    return B.CreateCall(openDecl(M),
                        {Path, ConstantInt::getSigned(I32, Flags),
                         ConstantInt::getSigned(I32, Mode)},
                        "morok.clean.open");
}

void emitDarwinClose(IRBuilder<> &B, Module &M, const Triple &TT, Value *Fd) {
    if (useDirectDarwinSyscalls(TT)) {
        emitDarwinSyscall(B, M, TT, 6, {Fd});
        return;
    }
    B.CreateCall(closeDecl(M), {B.CreateTruncOrBitCast(
                                   Fd, Type::getInt32Ty(M.getContext()))});
}

Value *emitDarwinLseek(IRBuilder<> &B, Module &M, const Triple &TT, Value *Fd,
                       std::int64_t Offset, std::int32_t Whence) {
    auto *I32 = Type::getInt32Ty(M.getContext());
    if (useDirectDarwinSyscalls(TT))
        return emitDarwinSyscall(B, M, TT, 199,
                                 {Fd, ConstantInt::getSigned(platformWordTy(M),
                                                             Offset),
                                  ConstantInt::getSigned(I32, Whence)});
    return B.CreateCall(lseekDecl(M),
                        {B.CreateTruncOrBitCast(Fd, I32),
                         ConstantInt::getSigned(platformWordTy(M), Offset),
                         ConstantInt::getSigned(I32, Whence)},
                        "morok.clean.lseek");
}

Value *emitDarwinMmap(IRBuilder<> &B, Module &M, const Triple &TT, Value *Size,
                      Value *Fd) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *IP = platformWordTy(M);
    auto *Ptr = PointerType::getUnqual(Ctx);
    constexpr std::uint32_t kProtRead = 1;
    constexpr std::uint32_t kMapPrivate = 2;

    if (useDirectDarwinSyscalls(TT)) {
        Value *Addr = emitDarwinSyscall(
            B, M, TT, 197,
            {ConstantPointerNull::get(Ptr), Size, ConstantInt::get(I32, kProtRead),
             ConstantInt::get(I32, kMapPrivate), Fd, ConstantInt::get(IP, 0)});
        return B.CreateIntToPtr(Addr, Ptr, "morok.clean.mmap.ptr");
    }

    return B.CreateCall(
        mmapDecl(M),
        {ConstantPointerNull::get(Ptr), Size, ConstantInt::get(I32, kProtRead),
         ConstantInt::get(I32, kMapPrivate), B.CreateTruncOrBitCast(Fd, I32),
         ConstantInt::get(IP, 0)},
        "morok.clean.mmap");
}

void emitDarwinMunmap(IRBuilder<> &B, Module &M, const Triple &TT,
                      Value *Mapped, Value *Size) {
    if (useDirectDarwinSyscalls(TT)) {
        emitDarwinSyscall(B, M, TT, 73, {Mapped, Size});
        return;
    }
    B.CreateCall(munmapDecl(M), {Mapped, Size});
}

Value *emitDarwinMprotect(IRBuilder<> &B, Module &M, const Triple &TT,
                          Value *Addr, Value *Size, Value *Prot) {
    auto *I32 = Type::getInt32Ty(M.getContext());
    if (useDirectDarwinSyscalls(TT))
        return B.CreateTruncOrBitCast(
            emitDarwinSyscall(B, M, TT, 74, {Addr, Size, Prot}), I32);

    auto *Ptr = PointerType::getUnqual(M.getContext());
    return B.CreateCall(mprotectDecl(M), {B.CreateIntToPtr(Addr, Ptr), Size,
                                          B.CreateTruncOrBitCast(Prot, I32)});
}

Value *emitPosixAnonMmapAddr(IRBuilder<> &B, Module &M, const Triple &TT,
                             Value *Size, Value *Prot, Value *Flags,
                             const Twine &Name) {
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *IP = platformWordTy(M);
    auto *Ptr = PointerType::getUnqual(Ctx);
    if (TT.isOSLinux() && useDirectLinuxSyscalls(TT))
        return emitLinuxSyscall(B, M, TT, 9,
                                {ConstantPointerNull::get(Ptr), Size, Prot,
                                 Flags, ConstantInt::getSigned(I32, -1),
                                 ConstantInt::get(IP, 0)});
    if (TT.isOSDarwin() && useDirectDarwinSyscalls(TT))
        return emitDarwinSyscall(B, M, TT, 197,
                                 {ConstantPointerNull::get(Ptr), Size, Prot,
                                  Flags, ConstantInt::getSigned(I32, -1),
                                  ConstantInt::get(IP, 0)});

    Value *Mapped = B.CreateCall(
        mmapDecl(M),
        {ConstantPointerNull::get(Ptr), Size, B.CreateTruncOrBitCast(Prot, I32),
         B.CreateTruncOrBitCast(Flags, I32), ConstantInt::getSigned(I32, -1),
         ConstantInt::get(IP, 0)},
        Name);
    return B.CreatePtrToInt(Mapped, IP, Name + ".addr");
}

Value *emitPosixMprotect(IRBuilder<> &B, Module &M, const Triple &TT,
                         Value *Addr, Value *Size, Value *Prot) {
    if (TT.isOSLinux())
        return emitLinuxMprotect(B, M, TT, Addr, Size, Prot);
    if (TT.isOSDarwin())
        return emitDarwinMprotect(B, M, TT, Addr, Size, Prot);
    return B.CreateCall(
        mprotectDecl(M),
        {B.CreateIntToPtr(Addr, PointerType::getUnqual(M.getContext())), Size,
         B.CreateTruncOrBitCast(Prot, Type::getInt32Ty(M.getContext()))});
}

} // namespace morok::runtime
