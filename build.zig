const std = @import("std");

const pkgs = struct {
    const clap = std.build.Pkg{
        .name = "clap",
        .path = .{ .path = "./zig-clap-0.5.0/clap.zig" },
        .dependencies = &[_]std.build.Pkg{},
    };
};

pub fn build(b: *std.build.Builder) void {
    // Standard release options allow the person running `zig build` to select
    // between Debug, ReleaseSafe, ReleaseFast, and ReleaseSmall.
    const mode = b.standardReleaseOptions();

    const lib = b.addStaticLibrary("tajzia", "src/main.zig");
    lib.setBuildMode(mode);
    lib.addPackage(pkgs.clap);
    lib.install();

    const main_tests = b.addTest("src/main.zig");
    main_tests.setBuildMode(mode);

    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&main_tests.step);

    const target = b.standardTargetOptions(.{});
    const exe = b.addExecutable("tajzia.exe", "src/main.zig");
    exe.setTarget(target);
    exe.linkLibrary(lib);
    exe.addPackage(pkgs.clap);
    exe.setBuildMode(mode);
    exe.install();

    const run_cmd = exe.run();
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the app");
    run_step.dependOn(&run_cmd.step);
}
