// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![deny(warnings)]

extern crate build_helper;
extern crate cc;

use std::env;
//use std::path::PathBuf;
use std::process::Command;
use build_helper::{run, native_lib_boilerplate};

fn main() {
    // FIXME: This is a hack to support building targets that don't
    // support jemalloc alongside hosts that do. The jemalloc build is
    // controlled by a feature of the std crate, and if that feature
    // changes between targets, it invalidates the fingerprint of
    // std's build script (this is a cargo bug); so we must ensure
    // that the feature set used by std is the same across all
    // targets, which means we have to build the alloc_jemalloc crate
    // for targets like emscripten, even if we don't use it.

    //let target = env::var("TARGET").expect("TARGET was not set");
    let host = env::var("HOST").expect("HOST was not set");

    println!("cargo:rustc-link-lib=pthread");

    let link_name = "ptmalloc";
    let native = match native_lib_boilerplate("ptmalloc2", "ptmalloc2", link_name, "") {
        Ok(native) => native,
        _ => return,
    };

//    let mut cmd = Command::new("sh");
//    cmd.arg(native.src_dir.join("configure")
//                          .to_str()
//                          .unwrap()
//                          .replace("C:\\", "/c/")
//                          .replace("\\", "/"))
//       .current_dir(&native.out_dir)
//       // jemalloc generates Makefile deps using GCC's "-MM" flag. This means
//       // that GCC will run the preprocessor, and only the preprocessor, over
//       // jemalloc's source files. If we don't specify CPPFLAGS, then at least
//       // on ARM that step fails with a "Missing implementation for 32-bit
//       // atomic operations" error. This is because no "-march" flag will be
//       // passed to GCC, and then GCC won't define the
//       // "__GCC_HAVE_SYNC_COMPARE_AND_SWAP_4" macro that jemalloc needs to
//       // select an atomic operation implementation.
//       .env("CPPFLAGS", env::var_os("CFLAGS").unwrap_or_default());
//
//    if target.contains("ios") {
//        cmd.arg("--disable-tls");
//    } else if target.contains("android") {
//        // We force android to have prefixed symbols because apparently
//        // replacement of the libc allocator doesn't quite work. When this was
//        // tested (unprefixed symbols), it was found that the `realpath`
//        // function in libc would allocate with libc malloc (not jemalloc
//        // malloc), and then the standard library would free with jemalloc free,
//        // causing a segfault.
//        //
//        // If the test suite passes, however, without symbol prefixes then we
//        // should be good to go!
//        cmd.arg("--with-jemalloc-prefix=je_");
//        cmd.arg("--disable-tls");
//    } else if target.contains("dragonfly") || target.contains("musl") {
//        cmd.arg("--with-jemalloc-prefix=je_");
//    }
//
//    if cfg!(feature = "debug") {
//        // Enable jemalloc assertions.
//        cmd.arg("--enable-debug");
//    }
//
//    cmd.arg(format!("--host={}", build_helper::gnu_target(&target)));
//    cmd.arg(format!("--build={}", build_helper::gnu_target(&host)));
//
//    // for some reason, jemalloc configure doesn't detect this value
//    // automatically for this target
//    if target == "sparc64-unknown-linux-gnu" {
//        cmd.arg("--with-lg-quantum=4");
//    }
//
//    run(&mut cmd);

    let mut make = Command::new(build_helper::make(&host));
    println!("{:?}", &native.src_dir);

    make.current_dir(&native.src_dir)
        .arg("linux-pthread")
        .env("LIBPATH", &native.out_dir);

//    // These are intended for mingw32-make which we don't use
//    if cfg!(windows) {
//        make.env_remove("MAKEFLAGS").env_remove("MFLAGS");
//    }
//
//    // mingw make seems... buggy? unclear...
//    if !host.contains("windows") {
//        make.arg("-j")
//            .arg(env::var("NUM_JOBS").expect("NUM_JOBS was not set"));
//    }

    run(&mut make);

    // The pthread_atfork symbols is used by jemalloc on android but the really
    // old android we're building on doesn't have them defined, so just make
    // sure the symbols are available.
//    if target.contains("androideabi") {
//        println!("cargo:rerun-if-changed=pthread_atfork_dummy.c");
//        cc::Build::new()
//            .flag("-fvisibility=hidden")
//            .file("pthread_atfork_dummy.c")
//            .compile("pthread_atfork_dummy");
//    }
}
