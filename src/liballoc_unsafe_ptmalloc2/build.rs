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
    //let target = env::var("TARGET").expect("TARGET was not set");
    let host = env::var("HOST").expect("HOST was not set");

    println!("cargo:rustc-link-lib=pthread");

    let link_name = "ptmalloc";
    let native = match native_lib_boilerplate("ptmalloc2", "ptmalloc2", link_name, "") {
        Ok(native) => native,
        _ => return,
    };

    let mut make = Command::new(build_helper::make(&host));
    println!("{:?}", &native.src_dir);

    // FIXME: This can only be compiled on linux right now
    make.current_dir(&native.src_dir)
        .arg("linux-pthread")
        // output the compiled binary to out_dir
        .env("LIBPATH", &native.out_dir);

    run(&mut make);
}
