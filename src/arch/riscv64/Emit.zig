//! This file contains the functionality for lowering RISCV64 MIR into
//! machine code

const Emit = @This();
const std = @import("std");
const math = std.math;
const Mir = @import("Mir.zig");
const bits = @import("bits.zig");
const link = @import("../../link.zig");
const Module = @import("../../Module.zig");
const ErrorMsg = Module.ErrorMsg;
const assert = std.debug.assert;
const Instruction = bits.Instruction;
const Register = bits.Register;
const DebugInfoOutput = @import("../../codegen.zig").DebugInfoOutput;

mir: Mir,
bin_file: *link.File,
debug_output: DebugInfoOutput,
target: *const std.Target,
err_msg: ?*ErrorMsg = null,
src_loc: Module.SrcLoc,
code: *std.ArrayList(u8),

prev_di_line: u32,
prev_di_column: u32,
/// Relative to the beginning of `code`.
prev_di_pc: usize,

const InnerError = error{
    OutOfMemory,
    EmitFail,
};

pub fn emitMir(
    emit: *Emit,
) InnerError!void {
    const mir_tags = emit.mir.instructions.items(.tags);

    // Emit machine code
    for (mir_tags, 0..) |tag, index| {
        const inst = @as(u32, @intCast(index));
        switch (tag) {
            .@"and",
            .add,
            .addw,
            .div,
            .divw,
            .divu,
            .divuw,
            .mul,
            .mulw,
            .mulh,
            .mulhsu,
            .mulhu,
            .nop,
            .@"or",
            .rem,
            .remw,
            .remu,
            .remuw,
            .sll,
            .sllw,
            .slt,
            .sra,
            .sraw,
            .srl,
            .srlw,
            .sltu,
            .sub,
            .subw,
            .xor,
            => try emit.mirRType(inst),

            .addi,
            .addiw,
            .andi,
            .csrrw,
            .csrrs,
            .csrrc,
            .csrrwi,
            .csrrci,
            .fence,
            .fence_i,
            .jalr,
            .lb,
            .lbu,
            .lh,
            .lhu,
            .lw,
            .lwu,
            .ld,
            .mv,
            .ori,
            .slli,
            .slliw,
            .srai,
            .sraiw,
            .srli,
            .srliw,
            .slti,
            .ret,
            .xori,
            => try emit.mirIType(inst),

            .sd, .sb, .sh, .sw => try emit.mirSType(inst),

            .beq, .bge, .blt, .bne => try emit.mirBType(inst),

            .jal => try emit.mirJType(inst),

            .ebreak, .ecall, .unimp => try emit.mirSystem(inst),

            .dbg_line => try emit.mirDbgLine(inst),

            .dbg_prologue_end => try emit.mirDebugPrologueEnd(),
            .dbg_epilogue_begin => try emit.mirDebugEpilogueBegin(),

            .auipc, .lui => try emit.mirUType(inst),
        }
    }
}

pub fn deinit(emit: *Emit) void {
    emit.* = undefined;
}

fn writeInstruction(emit: *Emit, instruction: Instruction) !void {
    const endian = emit.target.cpu.arch.endian();
    std.mem.writeInt(u32, try emit.code.addManyAsArray(4), instruction.toU32(), endian);
}

fn fail(emit: *Emit, comptime format: []const u8, args: anytype) InnerError {
    @setCold(true);
    assert(emit.err_msg == null);
    emit.err_msg = try ErrorMsg.create(emit.bin_file.allocator, emit.src_loc, format, args);
    return error.EmitFail;
}

fn dbgAdvancePCAndLine(self: *Emit, line: u32, column: u32) !void {
    const delta_line = @as(i32, @intCast(line)) - @as(i32, @intCast(self.prev_di_line));
    const delta_pc: usize = self.code.items.len - self.prev_di_pc;
    switch (self.debug_output) {
        .dwarf => |dw| {
            try dw.advancePCAndLine(delta_line, delta_pc);
            self.prev_di_line = line;
            self.prev_di_column = column;
            self.prev_di_pc = self.code.items.len;
        },
        .plan9 => |dbg_out| {
            if (delta_pc <= 0) return; // only do this when the pc changes
            // we have already checked the target in the linker to make sure it is compatable
            const quant = @import("../../link/Plan9/aout.zig").getPCQuant(self.target.cpu.arch) catch unreachable;

            // increasing the line number
            try @import("../../link/Plan9.zig").changeLine(dbg_out.dbg_line, delta_line);
            // increasing the pc
            const d_pc_p9 = @as(i64, @intCast(delta_pc)) - quant;
            if (d_pc_p9 > 0) {
                // minus one because if its the last one, we want to leave space to change the line which is one quanta
                try dbg_out.dbg_line.append(@as(u8, @intCast(@divExact(d_pc_p9, quant) + 128)) - quant);
                if (dbg_out.pcop_change_index.*) |pci|
                    dbg_out.dbg_line.items[pci] += 1;
                dbg_out.pcop_change_index.* = @as(u32, @intCast(dbg_out.dbg_line.items.len - 1));
            } else if (d_pc_p9 == 0) {
                // we don't need to do anything, because adding the quant does it for us
            } else unreachable;
            if (dbg_out.start_line.* == null)
                dbg_out.start_line.* = self.prev_di_line;
            dbg_out.end_line.* = line;
            // only do this if the pc changed
            self.prev_di_line = line;
            self.prev_di_column = column;
            self.prev_di_pc = self.code.items.len;
        },
        .none => {},
    }
}

fn mirRType(emit: *Emit, inst: Mir.Inst.Index) !void {
    const instruction = emit.mir.instructions.get(inst);

    switch (instruction) {
        .@"and" => |r_type| try emit.writeInstruction(Instruction.@"and"(r_type.rd, r_type.rs1, r_type.rs2)),
        .add => |r_type| try emit.writeInstruction(Instruction.add(r_type.rd, r_type.rs1, r_type.rs2)),
        .addw => |r_type| try emit.writeInstruction(Instruction.addw(r_type.rd, r_type.rs1, r_type.rs2)),
        .div => |r_type| try emit.writeInstruction(Instruction.div(r_type.rd, r_type.rs1, r_type.rs2)),
        .divw => |r_type| try emit.writeInstruction(Instruction.divw(r_type.rd, r_type.rs1, r_type.rs2)),
        .divu => |r_type| try emit.writeInstruction(Instruction.divu(r_type.rd, r_type.rs1, r_type.rs2)),
        .divuw => |r_type| try emit.writeInstruction(Instruction.divuw(r_type.rd, r_type.rs1, r_type.rs2)),
        .mul => |r_type| try emit.writeInstruction(Instruction.mul(r_type.rd, r_type.rs1, r_type.rs2)),
        .mulw => |r_type| try emit.writeInstruction(Instruction.mulw(r_type.rd, r_type.rs1, r_type.rs2)),
        .mulh => |r_type| try emit.writeInstruction(Instruction.mulh(r_type.rd, r_type.rs1, r_type.rs2)),
        .mulhsu => |r_type| try emit.writeInstruction(Instruction.mulhsu(r_type.rd, r_type.rs1, r_type.rs2)),
        .mulhu => |r_type| try emit.writeInstruction(Instruction.mulhu(r_type.rd, r_type.rs1, r_type.rs2)),
        .nop => try emit.writeInstruction(Instruction.addi(.zero, .zero, 0)),
        .@"or" => |r_type| try emit.writeInstruction(Instruction.@"or"(r_type.rd, r_type.rs1, r_type.rs2)),
        .rem => |r_type| try emit.writeInstruction(Instruction.rem(r_type.rd, r_type.rs1, r_type.rs2)),
        .remw => |r_type| try emit.writeInstruction(Instruction.remw(r_type.rd, r_type.rs1, r_type.rs2)),
        .remu => |r_type| try emit.writeInstruction(Instruction.remu(r_type.rd, r_type.rs1, r_type.rs2)),
        .remuw => |r_type| try emit.writeInstruction(Instruction.remuw(r_type.rd, r_type.rs1, r_type.rs2)),
        .sll => |r_type| try emit.writeInstruction(Instruction.sll(r_type.rd, r_type.rs1, r_type.rs2)),
        .sllw => |r_type| try emit.writeInstruction(Instruction.sllw(r_type.rd, r_type.rs1, r_type.rs2)),
        .slt => |r_type| try emit.writeInstruction(Instruction.slt(r_type.rd, r_type.rs1, r_type.rs2)),
        .sra => |r_type| try emit.writeInstruction(Instruction.sra(r_type.rd, r_type.rs1, r_type.rs2)),
        .sraw => |r_type| try emit.writeInstruction(Instruction.sraw(r_type.rd, r_type.rs1, r_type.rs2)),
        .srl => |r_type| try emit.writeInstruction(Instruction.srl(r_type.rd, r_type.rs1, r_type.rs2)),
        .srlw => |r_type| try emit.writeInstruction(Instruction.srlw(r_type.rd, r_type.rs1, r_type.rs2)),
        .sltu => |r_type| try emit.writeInstruction(Instruction.sltu(r_type.rd, r_type.rs1, r_type.rs2)),
        .sub => |r_type| try emit.writeInstruction(Instruction.sub(r_type.rd, r_type.rs1, r_type.rs2)),
        .subw => |r_type| try emit.writeInstruction(Instruction.subw(r_type.rd, r_type.rs1, r_type.rs2)),
        .xor => |r_type| try emit.writeInstruction(Instruction.xor(r_type.rd, r_type.rs1, r_type.rs2)),
        else => unreachable,
    }
}

fn mirIType(emit: *Emit, inst: Mir.Inst.Index) !void {
    const instruction = emit.mir.instructions.get(inst);

    switch (instruction) {
        .addi => |i_type| try emit.writeInstruction(Instruction.addi(i_type.rd, i_type.rs1, i_type.imm12)),
        .addiw => |i_type| try emit.writeInstruction(Instruction.addiw(i_type.rd, i_type.rs1, i_type.imm12)),
        .andi => |i_type| try emit.writeInstruction(Instruction.andi(i_type.rd, i_type.rs1, i_type.imm12)),
        .csrrw => |i_type| try emit.writeInstruction(Instruction.csrrw(i_type.rd, i_type.rs1, i_type.imm12)),
        .csrrs => |i_type| try emit.writeInstruction(Instruction.csrrs(i_type.rd, i_type.rs1, i_type.imm12)),
        .csrrc => |i_type| try emit.writeInstruction(Instruction.csrrc(i_type.rd, i_type.rs1, i_type.imm12)),
        .csrrwi => |i_type| try emit.writeInstruction(Instruction.csrrwi(i_type.rd, i_type.rs1, i_type.imm12)),
        .csrrci => |i_type| try emit.writeInstruction(Instruction.csrrci(i_type.rd, i_type.rs1, i_type.imm12)),
        .fence => |i_type| try emit.writeInstruction(Instruction.fence(i_type.imm12)),
        .fence_i => try emit.writeInstruction(Instruction.fence_i),
        .jalr => |i_type| try emit.writeInstruction(Instruction.jalr(i_type.rd, i_type.imm12, i_type.rs1)),
        .lb => |i_type| try emit.writeInstruction(Instruction.lb(i_type.rd, i_type.imm12, i_type.rs1)),
        .lbu => |i_type| try emit.writeInstruction(Instruction.lbu(i_type.rd, i_type.imm12, i_type.rs1)),
        .lh => |i_type| try emit.writeInstruction(Instruction.lh(i_type.rd, i_type.imm12, i_type.rs1)),
        .lhu => |i_type| try emit.writeInstruction(Instruction.lhu(i_type.rd, i_type.imm12, i_type.rs1)),
        .lw => |i_type| try emit.writeInstruction(Instruction.lw(i_type.rd, i_type.imm12, i_type.rs1)),
        .lwu => |i_type| try emit.writeInstruction(Instruction.lwu(i_type.rd, i_type.imm12, i_type.rs1)),
        .ld => |i_type| try emit.writeInstruction(Instruction.ld(i_type.rd, i_type.imm12, i_type.rs1)),
        .mv => |i_type| try emit.writeInstruction(Instruction.addi(i_type.rd, i_type.rs1, 0)),
        .ori => |i_type| try emit.writeInstruction(Instruction.ori(i_type.rd, i_type.rs1, i_type.imm12)),
        .slli => |i_type| try emit.writeInstruction(Instruction.slli(i_type.rd, i_type.rs1, i_type.imm12)),
        .slliw => |i_type| try emit.writeInstruction(Instruction.slliw(i_type.rd, i_type.rs1, i_type.imm12)),
        .srai => |i_type| try emit.writeInstruction(Instruction.srai(i_type.rd, i_type.rs1, i_type.imm12)),
        .sraiw => |i_type| try emit.writeInstruction(Instruction.sraiw(i_type.rd, i_type.rs1, i_type.imm12)),
        .srli => |i_type| try emit.writeInstruction(Instruction.srli(i_type.rd, i_type.rs1, i_type.imm12)),
        .srliw => |i_type| try emit.writeInstruction(Instruction.srliw(i_type.rd, i_type.rs1, i_type.imm12)),
        .slti => |i_type| try emit.writeInstruction(Instruction.slti(i_type.rd, i_type.rs1, i_type.imm12)),
        .ret => try emit.writeInstruction(Instruction.ret),
        .xori => |i_type| try emit.writeInstruction(Instruction.xori(i_type.rd, i_type.rs1, i_type.imm12)),
        else => unreachable,
    }
}

fn mirSType(emit: *Emit, inst: Mir.Inst.Index) !void {
    const instruction = emit.mir.instructions.get(inst);

    switch (instruction) {
        .sd => |s_type| try emit.writeInstruction(Instruction.sd(s_type.rs2, s_type.imm12, s_type.rs1)),
        .sb => |s_type| try emit.writeInstruction(Instruction.sb(s_type.rs2, s_type.imm12, s_type.rs1)),
        .sh => |s_type| try emit.writeInstruction(Instruction.sh(s_type.rs2, s_type.imm12, s_type.rs1)),
        .sw => |s_type| try emit.writeInstruction(Instruction.sw(s_type.rs2, s_type.imm12, s_type.rs1)),
        else => unreachable,
    }
}

fn mirBType(emit: *Emit, inst: Mir.Inst.Index) !void {
    const instruction = emit.mir.instructions.get(inst);

    switch (instruction) {
        .beq => |b_type| try emit.writeInstruction(Instruction.beq(b_type.rs1, b_type.rs2, b_type.imm)),
        .bge => |b_type| try emit.writeInstruction(Instruction.bge(b_type.rs1, b_type.rs2, b_type.imm)),
        .blt => |b_type| try emit.writeInstruction(Instruction.blt(b_type.rs1, b_type.rs2, b_type.imm)),
        .bne => |b_type| try emit.writeInstruction(Instruction.bne(b_type.rs1, b_type.rs2, b_type.imm)),
        else => unreachable,
    }
}

fn mirJType(emit: *Emit, inst: Mir.Inst.Index) !void {
    const instruction = emit.mir.instructions.get(inst);

    switch (instruction) {
        .jal => |j_type| try emit.writeInstruction(Instruction.jal(j_type.rd, j_type.imm20)),
        else => unreachable,
    }
}

fn mirSystem(emit: *Emit, inst: Mir.Inst.Index) !void {
    const tag = emit.mir.instructions.items(.tags)[inst];

    switch (tag) {
        .ebreak => try emit.writeInstruction(Instruction.ebreak),
        .ecall => try emit.writeInstruction(Instruction.ecall),
        .unimp => try emit.writeInstruction(Instruction.unimp),
        else => unreachable,
    }
}

fn mirDbgLine(emit: *Emit, inst: Mir.Inst.Index) !void {
    const dbg_line = emit.mir.instructions.get(inst);

    switch (dbg_line) {
        .dbg_line => |dbg_line_column| try emit.dbgAdvancePCAndLine(dbg_line_column.line, dbg_line_column.column),
        else => unreachable,
    }
}

fn mirDebugPrologueEnd(self: *Emit) !void {
    switch (self.debug_output) {
        .dwarf => |dw| {
            try dw.setPrologueEnd();
            try self.dbgAdvancePCAndLine(self.prev_di_line, self.prev_di_column);
        },
        .plan9 => {},
        .none => {},
    }
}

fn mirDebugEpilogueBegin(self: *Emit) !void {
    switch (self.debug_output) {
        .dwarf => |dw| {
            try dw.setEpilogueBegin();
            try self.dbgAdvancePCAndLine(self.prev_di_line, self.prev_di_column);
        },
        .plan9 => {},
        .none => {},
    }
}

fn mirUType(emit: *Emit, inst: Mir.Inst.Index) !void {
    const instruction = emit.mir.instructions.get(inst);

    switch (instruction) {
        .auipc => |u_type| try emit.writeInstruction(Instruction.auipc(u_type.rd, u_type.imm20)),
        .lui => |u_type| try emit.writeInstruction(Instruction.lui(u_type.rd, u_type.imm20)),
        else => unreachable,
    }
}
