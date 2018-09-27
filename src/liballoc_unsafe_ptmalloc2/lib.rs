// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![no_std]
#![allow(unused_attributes)]
#![unstable(feature = "alloc_unsafe_ptmalloc",
            reason = "implementation detail of std, does not provide any public API",
            issue = "0")]
#![feature(allocator_api)]
#![feature(core_intrinsics)]
#![cfg_attr(not(stage0), feature(nll))]
#![feature(staged_api)]
#![feature(rustc_attrs)]
#![feature(libc)]
// The minimum alignment guaranteed by the architecture. This value is used to
// add fast paths for low alignment values.
#[cfg(all(any(target_arch = "x86",
target_arch = "arm",
target_arch = "mips",
target_arch = "powerpc",
target_arch = "powerpc64",
target_arch = "asmjs",
target_arch = "wasm32")))]
#[allow(dead_code)]
const MIN_ALIGN: usize = 8;
#[cfg(all(any(target_arch = "x86_64",
target_arch = "aarch64",
target_arch = "mips64",
target_arch = "s390x",
target_arch = "sparc64")))]
#[allow(dead_code)]
const MIN_ALIGN: usize = 16;

use core::alloc::{Alloc, GlobalAlloc, AllocErr, Layout};
use core::ptr::NonNull;

pub use contents::*;
pub struct UnsafePtmalloc;

unsafe impl Alloc for UnsafePtmalloc {
    #[inline]
    unsafe fn alloc(&mut self, layout: Layout) -> Result<NonNull<u8>, AllocErr> {
        NonNull::new(GlobalAlloc::alloc(self, layout)).ok_or(AllocErr)
    }

    #[inline]
    unsafe fn unsafe_alloc(&mut self, layout: Layout) -> Result<NonNull<u8>, AllocErr> {
        NonNull::new(GlobalAlloc::unsafe_alloc(self, layout)).ok_or(AllocErr)
    }

    #[inline]
    unsafe fn alloc_zeroed(&mut self, layout: Layout) -> Result<NonNull<u8>, AllocErr> {
        NonNull::new(GlobalAlloc::alloc_zeroed(self, layout)).ok_or(AllocErr)
    }

    unsafe fn unsafe_alloc_zeroed(&mut self, layout: Layout) -> Result<NonNull<u8>, AllocErr> {
        NonNull::new(GlobalAlloc::unsafe_alloc_zeroed(self, layout)).ok_or(AllocErr)
    }

    #[inline]
    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
        GlobalAlloc::dealloc(self, ptr.as_ptr(), layout)
    }

    #[inline]
    unsafe fn realloc(&mut self, ptr: NonNull<u8>, layout: Layout, new_size: usize) -> Result<NonNull<u8>, AllocErr> {
        NonNull::new(GlobalAlloc::realloc(self, ptr.as_ptr(), layout, new_size)).ok_or(AllocErr)
    }
}
extern crate libc;

mod contents {
    use MIN_ALIGN;
    use UnsafePtmalloc;
    use core::alloc::{GlobalAlloc, Layout};

    use core::ptr;
    use core::cmp;

    // FIXME: only works on Linux
    use libc::{c_void, size_t};

    #[link(name = "ptmalloc", kind = "static")]
    extern "C" {
        fn pt_malloc(size: size_t) -> *mut c_void;
        fn pt_unsafe_malloc(size: size_t) -> *mut c_void;

        fn pt_calloc(nobj: size_t, size: size_t) -> *mut c_void;
        fn pt_unsafe_calloc(nobj: size_t, size: size_t) -> *mut c_void;

        fn pt_memalign(align: size_t, size: size_t) -> *mut c_void;
        fn pt_unsafe_memalign(align: size_t, size: size_t) -> *mut c_void;

        fn pt_realloc(p: *mut c_void, size: size_t) -> *mut c_void;

        fn pt_free(p : *mut c_void);
    }

    unsafe impl GlobalAlloc for UnsafePtmalloc {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            if layout.align() <= MIN_ALIGN && layout.align() <= layout.size() {
                pt_malloc(layout.size() as size_t) as *mut u8
            } else {
                pt_memalign(layout.align() as size_t, layout.size() as size_t) as *mut u8
            }
        }

        unsafe fn unsafe_alloc(&self, layout: Layout) -> *mut u8 {
            if layout.align() <= MIN_ALIGN && layout.align() <= layout.size() {
                pt_unsafe_malloc(layout.size() as size_t) as *mut u8
            } else {
                pt_unsafe_memalign(layout.align() as size_t, layout.size() as size_t) as *mut u8
            }
        }

        unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
            pt_free(ptr as *mut c_void)
        }

        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            if layout.align() <= MIN_ALIGN && layout.align() <= layout.size() {
                pt_calloc(layout.size() as size_t, 1 as size_t) as *mut u8
            } else {
                let ptr = self.alloc(layout.clone());
                if !ptr.is_null() {
                    ptr::write_bytes(ptr, 0, layout.size());
                }
                ptr
            }
        }

        unsafe fn unsafe_alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            if layout.align() <= MIN_ALIGN && layout.align() <= layout.size() {
                pt_unsafe_calloc(layout.size() as size_t, 1 as size_t) as *mut u8
            } else {
                let ptr = self.unsafe_alloc(layout.clone());
                if !ptr.is_null() {
                    ptr::write_bytes(ptr, 0, layout.size());
                }
                ptr
            }
        }

        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            if layout.align() <= MIN_ALIGN && layout.align() <= new_size {
                pt_realloc(ptr as *mut c_void, new_size as size_t) as *mut u8
            } else {
                // Docs for GlobalAlloc::realloc require this to be valid:
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());

                let new_ptr = GlobalAlloc::alloc(self, new_layout);
                if !new_ptr.is_null() {
                    let size = cmp::min(layout.size(), new_size);
                    ptr::copy_nonoverlapping(ptr, new_ptr, size);
                    GlobalAlloc::dealloc(self, ptr, layout);
                }
                new_ptr
            }
        }

    }
}
