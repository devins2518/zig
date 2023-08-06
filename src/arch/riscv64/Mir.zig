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
    mv: IType,
    nop,
    @"or": RType,
    ori: IType,
    rem: RType,
    remw: RType,
    remu: RType,
    remuw: RType,
    sd: SType,
    sb: SType,
    sh: SType,
    sll: RType,
    sllw: RType,
    slli: IType,
    slliw: IType,
    slt: RType,
    sra: RType,
    sraw: RType,
    srai: IType,
    sraiw: IType,
    srl: RType,
    srlw: RType,
    srli: IType,
    srliw: IType,
    slti: IType,
    sltu: RType,
    sub: RType,
    subw: RType,
    sw: SType,
    ret,
    unimp,
    xor: RType,
    xori: IType,

    pub const Tag = enum(u16) {
        @"and",
        add,
        addw,
        addi,
        addiw,
        andi,
        auipc,
        beq,
        bge,
        blt,
        bne,
        csrrw,
        csrrs,
        csrrc,
        csrrwi,
        csrrci,
        /// Pseudo-instruction: End of prologue
        dbg_prologue_end,
        /// Pseudo-instruction: Beginning of epilogue
        dbg_epilogue_begin,
        /// Pseudo-instruction: Update debug line
        dbg_line,
        div,
        divw,
        divu,
        divuw,
        ebreak,
        ecall,
        fence,
        fence_i,
        jal,
        jalr,
        lb,
        lbu,
        lh,
        lhu,
        lui,
        lw,
        lwu,
        ld,
        mul,
        mulw,
        mulh,
        mulhsu,
        mulhu,
        mv,
        nop,
        @"or",
        ori,
        rem,
        remw,
        remu,
        remuw,
        sd,
        sb,
        sh,
        sll,
        sllw,
        slli,
        slliw,
        slt,
        sra,
        sraw,
        srai,
        sraiw,
        srl,
        srlw,
        srli,
        srliw,
        slti,
        sltu,
        sub,
        subw,
        sw,
        ret,
        unimp,
        xor,
        xori,
    };

    /// The position of an MIR instruction within the `Mir` instructions array.
    pub const Index = u32;

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
