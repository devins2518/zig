const std = @import("std");
const Allocator = std.mem.Allocator;
const Module = @import("Module.zig");
const fs = std.fs;
const trace = @import("tracy.zig").trace;
const Package = @import("Package.zig");
const Type = @import("type.zig").Type;
const build_options = @import("build_options");

pub const producer_string = if (std.builtin.is_test) "zig test" else "zig " ++ build_options.version;

pub const Options = struct {
    dir: fs.Dir,
    /// Redundant with dir. Needed when linking with LLD because we have to pass paths rather
    /// than file descriptors. `null` means cwd. OK to pass `null` when `use_lld` is `false`.
    dir_path: ?[]const u8,
    /// Path to the output file, relative to dir.
    sub_path: []const u8,
    target: std.Target,
    output_mode: std.builtin.OutputMode,
    link_mode: std.builtin.LinkMode,
    object_format: std.builtin.ObjectFormat,
    optimize_mode: std.builtin.Mode,
    root_name: []const u8,
    root_pkg: ?*const Package,
    /// Used for calculating how much space to reserve for symbols in case the binary file
    /// does not already have a symbol table.
    symbol_count_hint: u64 = 32,
    /// Used for calculating how much space to reserve for executable program code in case
    /// the binary file does not already have such a section.
    program_code_size_hint: u64 = 256 * 1024,
    entry_addr: ?u64 = null,
    /// Set to `true` to omit debug info.
    strip: bool = false,
    /// If this is true then this link code is responsible for outputting an object
    /// file and then using LLD to link it together with the link options and other objects.
    /// Otherwise (depending on `use_llvm`) this link code directly outputs and updates the final binary.
    use_lld: bool = false,
    /// If this is true then this link code is responsible for making an LLVM IR Module,
    /// outputting it to an object file, and then linking that together with link options and
    /// other objects.
    /// Otherwise (depending on `use_lld`) this link code directly outputs and updates the final binary.
    use_llvm: bool = false,
    link_libc: bool = false,
    link_libcpp: bool = false,
    function_sections: bool = false,

    objects: []const []const u8 = &[0][]const u8{},
    framework_dirs: []const []const u8 = &[0][]const u8{},
    frameworks: []const []const u8 = &[0][]const u8{},
    system_libs: []const []const u8 = &[0][]const u8{},
    lib_dirs: []const []const u8 = &[0][]const u8{},
    rpath_list: []const []const u8 = &[0][]const u8{},

    pub fn effectiveOutputMode(options: Options) std.builtin.OutputMode {
        return if (options.use_lld) .Obj else options.output_mode;
    }
};

pub const File = struct {
    tag: Tag,
    options: Options,
    file: ?fs.File,
    allocator: *Allocator,
    /// When linking with LLD, this linker code will output an object file only at
    /// this location, and then this path can be placed on the LLD linker line.
    intermediary_basename: ?[]const u8 = null,

    pub const LinkBlock = union {
        elf: Elf.TextBlock,
        coff: Coff.TextBlock,
        macho: MachO.TextBlock,
        c: void,
        wasm: void,
    };

    pub const LinkFn = union {
        elf: Elf.SrcFn,
        coff: Coff.SrcFn,
        macho: MachO.SrcFn,
        c: void,
        wasm: ?Wasm.FnData,
    };

    /// For DWARF .debug_info.
    pub const DbgInfoTypeRelocsTable = std.HashMapUnmanaged(Type, DbgInfoTypeReloc, Type.hash, Type.eql, std.hash_map.DefaultMaxLoadPercentage);

    /// For DWARF .debug_info.
    pub const DbgInfoTypeReloc = struct {
        /// Offset from `TextBlock.dbg_info_off` (the buffer that is local to a Decl).
        /// This is where the .debug_info tag for the type is.
        off: u32,
        /// Offset from `TextBlock.dbg_info_off` (the buffer that is local to a Decl).
        /// List of DW.AT_type / DW.FORM_ref4 that points to the type.
        relocs: std.ArrayListUnmanaged(u32),
    };

    /// Attempts incremental linking, if the file already exists. If
    /// incremental linking fails, falls back to truncating the file and
    /// rewriting it. A malicious file is detected as incremental link failure
    /// and does not cause Illegal Behavior. This operation is not atomic.
    pub fn openPath(allocator: *Allocator, options: Options) !*File {
        const use_lld = build_options.have_llvm and options.use_lld; // comptime known false when !have_llvm
        const sub_path = if (use_lld) blk: {
            // Open a temporary object file, not the final output file because we want to link with LLD.
            break :blk try std.fmt.allocPrint(allocator, "{}{}", .{ options.sub_path, options.target.oFileExt() });
        } else options.sub_path;
        errdefer if (use_lld) allocator.free(sub_path);

        const file: *File = switch (options.object_format) {
            .coff, .pe => try Coff.openPath(allocator, sub_path, options),
            .elf => try Elf.openPath(allocator, sub_path, options),
            .macho => try MachO.openPath(allocator, sub_path, options),
            .wasm => try Wasm.openPath(allocator, sub_path, options),
            .c => try C.openPath(allocator, sub_path, options),
            .hex => return error.HexObjectFormatUnimplemented,
            .raw => return error.RawObjectFormatUnimplemented,
        };

        if (use_lld) {
            file.intermediary_basename = sub_path;
        }

        return file;
    }

    pub fn cast(base: *File, comptime T: type) ?*T {
        if (base.tag != T.base_tag)
            return null;

        return @fieldParentPtr(T, "base", base);
    }

    pub fn makeWritable(base: *File) !void {
        switch (base.tag) {
            .coff, .elf, .macho => {
                if (base.file != null) return;
                base.file = try base.options.dir.createFile(base.options.sub_path, .{
                    .truncate = false,
                    .read = true,
                    .mode = determineMode(base.options),
                });
            },
            .c, .wasm => {},
        }
    }

    pub fn makeExecutable(base: *File) !void {
        switch (base.tag) {
            .coff, .elf, .macho => if (base.file) |f| {
                if (base.intermediary_basename != null) {
                    // The file we have open is not the final file that we want to
                    // make executable, so we don't have to close it.
                    return;
                }
                f.close();
                base.file = null;
            },
            .c, .wasm => {},
        }
    }

    /// May be called before or after updateDeclExports but must be called
    /// after allocateDeclIndexes for any given Decl.
    pub fn updateDecl(base: *File, module: *Module, decl: *Module.Decl) !void {
        switch (base.tag) {
            .coff => return @fieldParentPtr(Coff, "base", base).updateDecl(module, decl),
            .elf => return @fieldParentPtr(Elf, "base", base).updateDecl(module, decl),
            .macho => return @fieldParentPtr(MachO, "base", base).updateDecl(module, decl),
            .c => return @fieldParentPtr(C, "base", base).updateDecl(module, decl),
            .wasm => return @fieldParentPtr(Wasm, "base", base).updateDecl(module, decl),
        }
    }

    pub fn updateDeclLineNumber(base: *File, module: *Module, decl: *Module.Decl) !void {
        switch (base.tag) {
            .coff => return @fieldParentPtr(Coff, "base", base).updateDeclLineNumber(module, decl),
            .elf => return @fieldParentPtr(Elf, "base", base).updateDeclLineNumber(module, decl),
            .macho => return @fieldParentPtr(MachO, "base", base).updateDeclLineNumber(module, decl),
            .c, .wasm => {},
        }
    }

    /// Must be called before any call to updateDecl or updateDeclExports for
    /// any given Decl.
    pub fn allocateDeclIndexes(base: *File, decl: *Module.Decl) !void {
        switch (base.tag) {
            .coff => return @fieldParentPtr(Coff, "base", base).allocateDeclIndexes(decl),
            .elf => return @fieldParentPtr(Elf, "base", base).allocateDeclIndexes(decl),
            .macho => return @fieldParentPtr(MachO, "base", base).allocateDeclIndexes(decl),
            .c, .wasm => {},
        }
    }

    pub fn deinit(base: *File) void {
        switch (base.tag) {
            .coff => @fieldParentPtr(Coff, "base", base).deinit(),
            .elf => @fieldParentPtr(Elf, "base", base).deinit(),
            .macho => @fieldParentPtr(MachO, "base", base).deinit(),
            .c => @fieldParentPtr(C, "base", base).deinit(),
            .wasm => @fieldParentPtr(Wasm, "base", base).deinit(),
        }
        if (base.file) |f| f.close();
        if (base.intermediary_basename) |sub_path| base.allocator.free(sub_path);
    }

    pub fn destroy(base: *File) void {
        switch (base.tag) {
            .coff => {
                const parent = @fieldParentPtr(Coff, "base", base);
                parent.deinit();
                base.allocator.destroy(parent);
            },
            .elf => {
                const parent = @fieldParentPtr(Elf, "base", base);
                parent.deinit();
                base.allocator.destroy(parent);
            },
            .macho => {
                const parent = @fieldParentPtr(MachO, "base", base);
                parent.deinit();
                base.allocator.destroy(parent);
            },
            .c => {
                const parent = @fieldParentPtr(C, "base", base);
                parent.deinit();
                base.allocator.destroy(parent);
            },
            .wasm => {
                const parent = @fieldParentPtr(Wasm, "base", base);
                parent.deinit();
                base.allocator.destroy(parent);
            },
        }
    }

    pub fn flush(base: *File, module: *Module) !void {
        const tracy = trace(@src());
        defer tracy.end();

        try switch (base.tag) {
            .coff => @fieldParentPtr(Coff, "base", base).flush(module),
            .elf => @fieldParentPtr(Elf, "base", base).flush(module),
            .macho => @fieldParentPtr(MachO, "base", base).flush(module),
            .c => @fieldParentPtr(C, "base", base).flush(module),
            .wasm => @fieldParentPtr(Wasm, "base", base).flush(module),
        };
    }

    pub fn freeDecl(base: *File, decl: *Module.Decl) void {
        switch (base.tag) {
            .coff => @fieldParentPtr(Coff, "base", base).freeDecl(decl),
            .elf => @fieldParentPtr(Elf, "base", base).freeDecl(decl),
            .macho => @fieldParentPtr(MachO, "base", base).freeDecl(decl),
            .c => unreachable,
            .wasm => @fieldParentPtr(Wasm, "base", base).freeDecl(decl),
        }
    }

    pub fn errorFlags(base: *File) ErrorFlags {
        return switch (base.tag) {
            .coff => @fieldParentPtr(Coff, "base", base).error_flags,
            .elf => @fieldParentPtr(Elf, "base", base).error_flags,
            .macho => @fieldParentPtr(MachO, "base", base).error_flags,
            .c => return .{ .no_entry_point_found = false },
            .wasm => return ErrorFlags{},
        };
    }

    /// May be called before or after updateDecl, but must be called after
    /// allocateDeclIndexes for any given Decl.
    pub fn updateDeclExports(
        base: *File,
        module: *Module,
        decl: *const Module.Decl,
        exports: []const *Module.Export,
    ) !void {
        switch (base.tag) {
            .coff => return @fieldParentPtr(Coff, "base", base).updateDeclExports(module, decl, exports),
            .elf => return @fieldParentPtr(Elf, "base", base).updateDeclExports(module, decl, exports),
            .macho => return @fieldParentPtr(MachO, "base", base).updateDeclExports(module, decl, exports),
            .c => return {},
            .wasm => return @fieldParentPtr(Wasm, "base", base).updateDeclExports(module, decl, exports),
        }
    }

    pub fn getDeclVAddr(base: *File, decl: *const Module.Decl) u64 {
        switch (base.tag) {
            .coff => return @fieldParentPtr(Coff, "base", base).getDeclVAddr(decl),
            .elf => return @fieldParentPtr(Elf, "base", base).getDeclVAddr(decl),
            .macho => return @fieldParentPtr(MachO, "base", base).getDeclVAddr(decl),
            .c => unreachable,
            .wasm => unreachable,
        }
    }

    pub const Tag = enum {
        coff,
        elf,
        macho,
        c,
        wasm,
    };

    pub const ErrorFlags = struct {
        no_entry_point_found: bool = false,
    };

    pub const C = @import("link/C.zig");
    pub const Coff = @import("link/Coff.zig");
    pub const Elf = @import("link/Elf.zig");
    pub const MachO = @import("link/MachO.zig");
    pub const Wasm = @import("link/Wasm.zig");
};

pub fn determineMode(options: Options) fs.File.Mode {
    // On common systems with a 0o022 umask, 0o777 will still result in a file created
    // with 0o755 permissions, but it works appropriately if the system is configured
    // more leniently. As another data point, C's fopen seems to open files with the
    // 666 mode.
    const executable_mode = if (std.Target.current.os.tag == .windows) 0 else 0o777;
    switch (options.effectiveOutputMode()) {
        .Lib => return switch (options.link_mode) {
            .Dynamic => executable_mode,
            .Static => fs.File.default_mode,
        },
        .Exe => return executable_mode,
        .Obj => return fs.File.default_mode,
    }
}
