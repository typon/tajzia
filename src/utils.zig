const std = @import("std");
const log = std.log;
const print = @import("std").debug.print;

pub fn log_empty_line() void {
    if (log.level == log.Level.debug) {
        print("\n", .{});
    }
}
