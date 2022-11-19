// Modules
const std = @import("std");

// Global constants
const stdout = std.io.getStdOut().writer();
// Global types
const Allocator = std.mem.Allocator;
const ArLs = std.ArrayList;

// Femto-language for testing
const Prog = ArLs(Instr);
const Instr = struct {
    op: Op,
    jnz_r: isize = 1,
};
const Op = enum {
    nops,
    nopi, // no-op set flag, no-op invert flag
    inc,
    dec, // increment reg, decrement reg
    star,
    nl, // print star, print newline
    crash, // crash
};

// Types for concolic execution
const PathCond = ArLs(SymExpr);
const SymExpr = union(enum) {
    op: Op,
    constraint: bool,
};
const Trace = struct {
    path: PathCond,
    crashes: bool,

    pub fn deinit() void {
        @This().path.deinit();
    }
};

// Perform concolic execution of a program in the femto-language
// This returns a crashing input if it can find one
fn run_concolic(heap: Allocator, prog: Prog, seed_input: i32) anyerror!?i32 {
    if (!try run_program(prog, seed_input, true)) return seed_input;
    var alt_stack = ArLs(usize).init(heap);
    defer alt_stack.deinit();
    var desired_path = PathCond.init(heap);
    defer desired_path.deinit();
    {
        const trace_path = (try create_trace(heap, prog, seed_input)).path;
        defer trace_path.deinit();
        var index: usize = 0;
        for (trace_path.items) |item| {
            switch (item) {
                .constraint => try alt_stack.append(index),
                else => {},
            }
            try desired_path.append(item);
            index += 1;
        }
    }
    while (alt_stack.items.len > 0) {
        const inv_index = alt_stack.pop();
        const orig_expr = desired_path.items[inv_index];
        try desired_path.resize(inv_index);
        try desired_path.append(SymExpr{ .constraint = !orig_expr.constraint });
        const new_input = solve_input(desired_path);
        if (new_input == null) continue;
        const trace = try create_trace(heap, prog, new_input.?);
        if (trace.crashes) {
            trace.path.deinit();
            return new_input.?;
        }
        desired_path.deinit();
        desired_path = trace.path;
        {
            var index = inv_index + 1;
            while (index < desired_path.items.len) : (index += 1) {
                switch (desired_path.items[index]) {
                    .constraint => try alt_stack.append(index),
                    else => {},
                }
            }
        }
    }
    return null;
}

// Run a program in the femto-language and return a trace
fn create_trace(heap: Allocator, prog: Prog, input: i32) anyerror!Trace {
    try stdout.print("Tracing input {d}...\n", .{input});
    var path_cond = PathCond.init(heap);
    errdefer path_cond.deinit();
    var reg = input;
    var flag = input != 0;
    var inptr: isize = 0;
    var itercount: u16 = 0;
    while (inptr < prog.items.len) : (itercount += 1) {
        if (itercount > 500) return Trace{
            .path = path_cond,
            .crashes = false,
        };
        const item = prog.items[@intCast(usize, inptr)];
        var track_op = true;
        switch (item.op) {
            Op.nops => flag = true,
            Op.nopi => flag = !flag,
            Op.inc => {
                reg += 1;
                flag = reg != 0;
            },
            Op.dec => {
                reg -= 1;
                flag = reg != 0;
            },
            Op.crash => return Trace{
                .path = path_cond,
                .crashes = true,
            },
            else => track_op = false,
        }
        if (track_op) {
            try path_cond.append(SymExpr{ .op = item.op });
        }
        if (item.jnz_r == 1) {
            inptr += 1;
        } else {
            try path_cond.append(SymExpr{ .constraint = flag });
            inptr += if (flag) item.jnz_r else 1;
        }
    }
    return Trace{
        .path = path_cond,
        .crashes = false,
    };
}

// Solve for an input that produces the desired path condition
fn solve_input(path_cond: PathCond) ?i32 {
    var reg_relative: i32 = 0;
    var demanded_zero: ?i32 = null;
    var demanded_nz_max: ?i32 = null;
    var inverted = false;
    var forced = false;
    for (path_cond.items) |item| {
        switch (item) {
            .op => switch (item.op) {
                Op.nops => forced = true,
                Op.nopi => inverted = !inverted,
                Op.inc => {
                    reg_relative += 1;
                    forced = false;
                },
                Op.dec => {
                    reg_relative -= 1;
                    forced = false;
                },
                Op.crash => return null,
                else => {},
            },
            .constraint => {
                var desired_state = item.constraint;
                if (inverted) desired_state = !desired_state;
                if (forced and !desired_state) return null;
                if (desired_state) {
                    if (demanded_nz_max == null) {
                        demanded_nz_max = reg_relative;
                    } else {
                        demanded_nz_max = @max(demanded_nz_max.?, reg_relative);
                    }
                } else {
                    if (demanded_zero != null) return null;
                    demanded_zero = reg_relative;
                }
            },
        }
    }
    if (demanded_zero == null and demanded_nz_max == null)
        return 42;
    if (demanded_zero != null and demanded_nz_max == null)
        return -demanded_zero.?;
    if (demanded_zero == null and demanded_nz_max != null)
        return (-demanded_nz_max.?) - 1;
    const target = -demanded_zero.?;
    if (satisfying_input(target, path_cond))
        return target;
    return null;
}

// Check if an input satisfies a path condition
fn satisfying_input(input: i32, path_cond: PathCond) bool {
    var reg = input;
    var flag = input != 0;
    var itercount: u16 = 0;
    for (path_cond.items) |item| {
        if (itercount > 500) return true;
        switch (item) {
            .op => switch (item.op) {
                Op.nops => flag = true,
                Op.nopi => flag = !flag,
                Op.inc => {
                    reg += 1;
                    flag = reg != 0;
                },
                Op.dec => {
                    reg -= 1;
                    flag = reg != 0;
                },
                else => {},
            },
            .constraint => {
                if (flag != item.constraint) return false;
            },
        }
        itercount += 1;
    }
    return true;
}

// Run a program in the femto-language
fn run_program(prog: Prog, input: i32, silent: bool) anyerror!bool {
    var reg = input;
    var flag = input != 0;
    var inptr: isize = 0;
    var itercount: u16 = 0;
    while (inptr < prog.items.len) : (itercount += 1) {
        if (itercount > 500) {
            try stdout.print("<TOOLONG>\n", .{});
            return true;
        }
        const item = prog.items[@intCast(usize, inptr)];
        switch (item.op) {
            Op.nops => flag = true,
            Op.nopi => flag = !flag,
            Op.inc => {
                reg += 1;
                flag = reg != 0;
            },
            Op.dec => {
                reg -= 1;
                flag = reg != 0;
            },
            Op.star => if (!silent) try stdout.print("*", .{}),
            Op.nl => if (!silent) try stdout.print("\n", .{}),
            Op.crash => {
                try stdout.print("<CRASH>\n", .{});
                return false;
            },
        }
        inptr += if (flag) item.jnz_r else 1;
    }
    return true;
}

// Main function (given an allocator)
fn main_with_heap(heap: Allocator) anyerror!void {
    var example = Prog.init(heap);
    defer example.deinit();
    try example.appendSlice(&[_]Instr{
        Instr{ .op = Op.nopi, .jnz_r = 4 },
        Instr{ .op = Op.star },
        Instr{ .op = Op.dec, .jnz_r = -2 },
        Instr{ .op = Op.nops, .jnz_r = 2 },
        Instr{ .op = Op.crash },
        Instr{ .op = Op.nl },
    });
    try stdout.print("Example given 3: ", .{});
    _ = try run_program(example, 3, false);
    try stdout.print("Running concolic execution...\n", .{});
    const errorcase = try run_concolic(heap, example, 3);
    if (errorcase == null) {
        try stdout.print("No erronous cases found.\n", .{});
    } else {
        const input = errorcase.?;
        try stdout.print("Found erronous case {d}.\n", .{input});
        try stdout.print("Example given {d} (should fail): ", .{input});
        _ = try run_program(example, input, false);
    }
}

test "can find bug" {
    var heap = std.testing.allocator;
    var example = Prog.init(heap);
    defer example.deinit();
    try example.appendSlice(&[_]Instr{
        Instr{ .op = Op.nopi, .jnz_r = 4 },
        Instr{ .op = Op.star },
        Instr{ .op = Op.dec, .jnz_r = -2 },
        Instr{ .op = Op.nops, .jnz_r = 2 },
        Instr{ .op = Op.crash },
        Instr{ .op = Op.nl },
    });
    const errorcase = try run_concolic(heap, example, 3);
    try std.testing.expect(errorcase != null);
    try std.testing.expect(!try run_program(example, errorcase.?, true));
}

// Main function (entry point)
pub fn main() anyerror!void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const heap = gpa.allocator();
    defer {
        if (gpa.deinit()) @panic("Leak Detected");
    }
    try main_with_heap(heap);
}
