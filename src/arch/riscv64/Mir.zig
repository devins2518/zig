//! Machine Intermediate Representation.
//! This data is produced by RISCV64 Codegen or RISCV64 assembly parsing
//! These instructions have a 1:1 correspondence with machine code instructions
//! for the target. MIR can be lowered to source-annotated textual assembly code
//! instructions, or it can be lowered to machine code.
//! The main purpose of MIR is to postpone the assignment of offsets until Isel,
//! so that, for example, the smaller encodings of jump instructions can be used.

const Mir = @This();
const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;

const bits = @import("bits.zig");
const Register = bits.Register;

instructions: std.MultiArrayList(Inst).Slice,
/// The meaning of this data is determined by `Inst.Tag` value.
extra: []const u32,

pub const Inst = union(Tag) {
    @"and": RType,
    add: RType,
    addw: RType,
    addi: IType,
    addiw: IType,
    andi: IType,
    auipc: UType,
    beq: BType,
    bge: BType,
    blt: BType,
    bne: BType,
    csrrw: IType,
    csrrs: IType,
    csrrc: IType,
    csrrwi: IType,
    csrrsi: IType,
    csrrci: IType,
    dbg_prologue_end,
    dbg_epilogue_begin,
    dbg_line: DbgLineColumn,
    div: RType,
    divw: RType,
    divu: RType,
    divuw: RType,
    ebreak,
    ecall,
    fence: IType, // TODO: wrong, custom format
    fence_i: IType,
    jal: JType,
    jalr: IType,
    lb: IType,
    lbu: IType,
    lh: IType,
    lhu: IType,
    lui: UType,
    lw: IType,
    lwu: IType,
    ld: IType,
    mul: RType,
    mulw: RType,
    mulh: RType,
    mulhsu: RType,
    mulhu: RType,
    mv: RRType,
    nop,
    @"or": RType,
    ori: IType,
    rem: RType,
    remw: RType,
    remu: RType,
    remuw: RType,
    sb: SType,
    sd: SType,
    seq: RType,
    seqz: RRType,
    sgt: RType,
    sgtu: RType,
    sgte: RType,
    sgteu: RType,
    sh: SType,
    sneq: RType,
    sll: RType,
    sllw: RType,
    slli: IType,
    slliw: IType,
    slt: RType,
    sltu: RType,
    slte: RType,
    slteu: RType,
    slti: IType,
    snez: RRType,
    sra: RType,
    sraw: RType,
    srai: IType,
    sraiw: IType,
    srl: RType,
    srlw: RType,
    srli: IType,
    srliw: IType,
    sub: RType,
    subw: RType,
    sw: SType,
    ret,
    unimp,
    xor: RType,
    xori: IType,

    pub const Tag = enum(u16) {
        /// Bitwise and
        @"and",
        /// 64 bit addition
        add,
        /// 32 bit addition
        addw,
        /// 64 bit addition with immediate
        addi,
        /// 32 bit addition with immediate
        addiw,
        /// Bitwise and
        andi,
        /// Add unsigned immediate to PC
        auipc,
        /// Branch if equal
        beq,
        /// Branch if greater than or equal
        bge,
        /// Branch if less than
        blt,
        /// Branch if not equal to
        bne,
        /// Atomically read/write CSR
        csrrw,
        /// Atomically read/set bits CSR
        csrrs,
        /// Atomically read/clear bits CSR
        csrrc,
        /// Atomically read/write CSR from immediate
        csrrwi,
        /// Atomically read/set bits CSR from immediate
        csrrsi,
        /// Atomically read/clear bits CSR from immediate
        csrrci,
        /// Pseudo-instruction: End of prologue
        dbg_prologue_end,
        /// Pseudo-instruction: Beginning of epilogue
        dbg_epilogue_begin,
        /// Pseudo-instruction: Update debug line
        dbg_line,
        /// 64-bit signed division
        div,
        /// 32-bit signed division
        divw,
        /// 64-bit unsigned division
        divu,
        /// 32-bit unsigned division
        divuw,
        /// Causes control to be handed back to debugger
        ebreak,
        /// System call
        ecall,
        /// Used to fence IO and memory transactions as viewed by other HARTs
        fence,
        /// Used to fence instruction memory transactions as viewed by other HARTs
        fence_i,
        /// Jump immediate and set return address in link register
        jal,
        /// Jump register and set return address in link register
        jalr,
        /// Load byte from memory
        lb,
        /// Load unsigned byte from memory
        lbu,
        /// Load double word from memory
        ld,
        /// Load half word from memory
        lh,
        /// Load unsigned half word from memory
        lhu,
        /// Load upper immediate into register
        lui,
        /// Load word from memory
        lw,
        /// Load unsigned word from memory
        lwu,
        /// 64-bit multiplication setting lower 32-bits
        mul,
        /// 32-bit multiplication
        mulw,
        /// 64-bit signed-signed multiplication setting upper 32-bits
        mulh,
        /// 64-bit signed-unsigned multiplication setting upper 32-bits
        mulhsu,
        /// 64-bit unsigned-unsigned multiplication setting upper 32-bits
        mulhu,
        /// Pseudo-instruction: Move register
        mv,
        /// Pseudo-instruction: Noop
        nop,
        /// Bitwise or
        @"or",
        /// Bitwise or immediate
        ori,
        /// 64-bit signed remainder
        rem,
        /// 32-bit signed remainder
        remw,
        /// 64-bit unsigned remainder
        remu,
        /// 32-bit unsigned remainder
        remuw,
        /// Store byte to memory
        sb,
        /// Store double word to memory
        sd,
        /// Pseudo-instruction: Set if equal
        seq,
        /// Pseudo-instruction: Set if equal to zero
        seqz,
        /// Pseudo-isntruction: Set if greater than
        sgt,
        /// Pseudo-isntruction: Set if greater than or equal
        sgte,
        /// Pseudo-isntruction: Set if unsigned greater than
        sgtu,
        /// Pseudo-isntruction: Set if unsigned greater than or equal
        sgteu,
        /// Store half word to memory
        sh,
        /// 64-bit shift left logical
        sll,
        /// 32-bit shift left logical
        sllw,
        /// 64-bit shift left logical by immediate
        slli,
        /// 32-bit shift left logical by immediate
        slliw,
        /// Set if less than
        slt,
        /// Set to immediate if unsigned less than
        sltu,
        /// Pseudo-instruction: Set if less than or equal to
        slte,
        /// Pseudo-instruction: Set if unsigned less than or equal to
        slteu,
        /// Pseudo-instruction: Set if not equal to
        sneq,
        /// Pseudo-instruction: Set if not equal to zero
        snez,
        /// 64-bit shift right arithmetic
        sra,
        /// 32-bit shift right arithmetic
        sraw,
        /// 64-bit shift right arithmetic by immediate
        srai,
        /// 32-bit shift right arithmetic by immediate
        sraiw,
        /// 64-bit shift right logical
        srl,
        /// 32-bit shift right logical
        srlw,
        /// 64-bit shift right logical by immediate
        srli,
        /// 32-bit shift right logical by immediate
        srliw,
        /// Set to immediate if less than
        slti,
        /// 64-bit subtraction
        sub,
        /// 32-bit subtraction
        subw,
        /// Store word to memory
        sw,
        /// Pseudo-instruction: return from function
        ret,
        /// Pseudo-instruction: trigger illegal instruction exception
        unimp,
        /// Bitwise exclusive or
        xor,
        /// Bitwise exclusive or immediate
        xori,
    };

    /// The position of an MIR instruction within the `Mir` instructions array.
    pub const Index = u32;

    /// R-R Type (to be used only for pseudo-instructions)
    ///
    /// Used in e.g. mv
    pub const RRType = struct {
        rd: Register,
        rs1: Register,
    };

    /// I-Type
    ///
    /// Used by e.g. jalr
    pub const IType = struct {
        rd: Register,
        rs1: Register,
        imm12: i12,
    };
    /// R-Type
    ///
    /// Used by e.g. add
    pub const RType = struct {
        rd: Register,
        rs1: Register,
        rs2: Register,
    };
    /// U-Type
    ///
    /// Used by e.g. lui
    pub const UType = struct {
        rd: Register,
        imm20: i20,
    };
    /// J-Type
    ///
    /// Used by e.g. jal
    pub const JType = struct {
        rd: Register,
        imm20: i20,
    };
    /// S-Type
    ///
    /// Used by e.g. sw
    pub const SType = struct {
        rs1: Register,
        rs2: Register,
        imm12: i12,
    };
    /// B-Type
    ///
    /// Used by e.g. beq
    pub const BType = struct {
        rs1: Register,
        rs2: Register,
        imm: i12,
    };
    /// Debug info: line and column
    ///
    /// Used by e.g. dbg_line
    pub const DbgLineColumn = struct {
        line: u32,
        column: u32,
    };

    // Make sure we don't accidentally make instructions bigger than expected.
    // Note that in Debug builds, Zig is allowed to insert a secret field for safety checks.
    // comptime {
    //     if (builtin.mode != .Debug) {
    //         assert(@sizeOf(Inst) == 8);
    //     }
    // }
};

pub fn deinit(mir: *Mir, gpa: std.mem.Allocator) void {
    mir.instructions.deinit(gpa);
    gpa.free(mir.extra);
    mir.* = undefined;
}

/// Returns the requested data, as well as the new index which is at the start of the
/// trailers for the object.
pub fn extraData(mir: Mir, comptime T: type, index: usize) struct { data: T, end: usize } {
    const fields = std.meta.fields(T);
    var i: usize = index;
    var result: T = undefined;
    inline for (fields) |field| {
        @field(result, field.name) = switch (field.type) {
            u32 => mir.extra[i],
            i32 => @as(i32, @bitCast(mir.extra[i])),
            else => @compileError("bad field type"),
        };
        i += 1;
    }
    return .{
        .data = result,
        .end = i,
    };
}
