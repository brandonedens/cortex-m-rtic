//! examples/rtos.rs

//#![deny(warnings)]
#![no_main]
#![no_std]
#![feature(asm)]
#![feature(naked_functions)]

use core::sync::atomic::{AtomicUsize, Ordering};

use cortex_m_semihosting::{debug, hprintln};
use heapless::consts::U8;
use heapless::Vec;
use panic_semihosting as _;

struct Thread {
    /// Stack of thread priorities (priority inversion)
    priorities: Vec<u8, U8>,
    /// The last time this thread executed.
    last_exec: usize,
    stack: [u8; 512],
    stack_top: u32,
    entry: fn(),
}

impl Thread {
    fn new(entry_fn: fn()) -> Self {
        // TODO we ave to set up stack_top and initial stack contents.
        let thread = Thread {
            priorities: Vec::new(),
            last_exec: 0,
            stack: [0u8; 512],
            stack_top: 0,
            entry: entry_fn,
        };
        thread
    }
}

pub struct Rtos {
    semaphores: [AtomicUsize; 2],
    cur_thread: Option<usize>,
    threads: [Option<Thread>; 3],
    runnable: [Option<usize>; 3],
    blocked: [Option<usize>; 3],
    need_reschedule: bool,
}

impl Default for Rtos {
    fn default() -> Self {
        Rtos {
            semaphores: [AtomicUsize::new(0), AtomicUsize::new(0)],
            cur_thread: None,
            threads: [None, None, None],
            runnable: [None, None, None],
            blocked: [None, None, None],
            need_reschedule: false,
        }
    }
}

impl Rtos {
    /// Execute the RTOS making forward progress in work.
    fn execute(&mut self) {}

    /// Reschedule which thread executes next.
    fn reschedule(&mut self) {
        // Find thread with highest priority that is runnable.
        if let Some(idx) = self.runnable.iter().filter_map(|v| *v).max_by(|a, b| {
            // Note that we've already filtered out None.
            if let (Some(thread_a), Some(thread_b)) =
                (self.threads[*a].as_ref(), self.threads[*b].as_ref())
            {
                if thread_a.priorities[0] == thread_b.priorities[0] {
                    if thread_a.last_exec < thread_b.last_exec {
                        core::cmp::Ordering::Greater
                    } else {
                        core::cmp::Ordering::Less
                    }
                } else if thread_a.priorities[0] > thread_b.priorities[0] {
                    core::cmp::Ordering::Greater
                } else {
                    core::cmp::Ordering::Less
                }
            } else {
                core::cmp::Ordering::Less
            }
        }) {
            if let Some(thread) = &self.threads[idx] {
                self.cur_thread = Some(idx);
            } else {
                self.cur_thread = None;
            }
        }
    }

    fn semaphore_get(&mut self, idx: usize) {
        loop {
            let cur_val = self.semaphores[idx].load(Ordering::SeqCst);
            if cur_val == 0 {
                // Yield the executing thread which is now waiting on the semaphore.
            }
            if let Ok(prev) = self.semaphores[idx].compare_exchange(
                cur_val,
                cur_val - 1,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                break;
            }
        }
    }

    fn semaphore_put(&mut self, idx: usize) {
        let prev_value = self.semaphores[idx].fetch_add(1, Ordering::SeqCst);
        if prev_value == 0 {
            // Trip a pending supervisor call to potentially reschedule.
            cortex_m::peripheral::SCB::set_pendsv();
        }
    }
}

#[naked]
fn thread_exit() {
    unsafe { asm!("svc 1"); }
}

#[naked]
fn thread_yield() {
    unsafe { asm!("svc 2"); }
}

#[naked]
fn thread_sleep(ticks: usize) {
    unsafe { asm!("svc 3"); }
}

/// Get the semaphore. Note that this function might block the thread of execution.
#[naked]
fn semaphore_get(idx: usize) {
    unsafe { asm!("svc 4"); }
}

#[naked]
fn semaphore_put(idx: usize) {
    unsafe { asm!("svc 5"); }
}

fn thread_a() {
    let mut x = 1;
    for i in 0..100 {
        semaphore_get(0);
        for i in 0..500 {
            x *= i;
        }
        semaphore_put(0);
        thread_sleep(3);
    }
}

fn thread_b() {
    let mut x = 1;
    for i in 0..100 {
        semaphore_get(0);
        semaphore_get(1);
        for i in 0..100 {
            x += i;
        }
        semaphore_put(1);
        semaphore_put(0);
        thread_sleep(2);
    }
}

fn thread_c() {
    let mut x = 42;
    for i in 0..1000 {
        semaphore_get(1);
        for i in 0..50 {
            x += i;
        }
        semaphore_put(1);
        thread_sleep(1);
    }
}

#[allow(non_snake_case)]
#[no_mangle]
#[naked]
unsafe fn PendSV() {
        // Save the context of scratch registers to PSP or MSP.
        asm!(
            "tst lr, #4
             bne.n 1f
             mrs r1, msp
             stmdb r1!, {{r4-r11}}
             msr msp, r1
             b 2f
             1:
             mrs r1, psp
             stmdb r1!, {{r4-r11}}
             msr psp, r1
             2:",
            out("r0") _,
            out("r1") _,
        );
    const PRIORITY: u8 = 0u8;
    rtic::export::run(PRIORITY, || {
        crate::pendsv(pendsv::Context::new(&rtic::export::Priority::new(PRIORITY)))
    });

    let psp = cortex_m::register::psp::read();
    if psp != 0 {
        // Restore context from PSP and set thread execution with PSP.
        asm!("mrs r0, psp
            ldmdb r0!, {{r4-r11}}
            msr psp, r0
            mov r0, #0xFFFFFFED
            mov lr, r0",
            out("r0") _,
        );
    } else {
        // Branch to handler execution with MSP to invoke idle.
        asm!("mov r0, #0xFFFFFFE1
            mov lr, r0",
            out("r0") _,
        );
    }
}

#[rtic::app(device = lm3s6965)]
const APP: () = {
    struct Resources {
        rtos: Rtos,
    }

    #[init]
    fn init(_: init::Context) -> init::LateResources {
        hprintln!("init").unwrap();

        // Create three threads.
        let mut rtos = Rtos::default();
        rtos.threads[0] = Some(Thread::new(thread_a));
        rtos.threads[1] = Some(Thread::new(thread_b));
        rtos.threads[2] = Some(Thread::new(thread_c));
        // TODO thread_c needs to be highest priority to demo priority inversion.

        init::LateResources { rtos }
    }

    #[task(resources = [rtos])]
    fn pendsv(cx: pendsv::Context) {
        hprintln!("pendsv").unwrap();
        cx.resources.rtos.reschedule();
        if let Some(cur_thread_idx) = cx.resources.rtos.cur_thread {
            if let Some(cur_thread) = cx.resources.rtos.threads[cur_thread_idx].as_ref() {
                unsafe {
                    cortex_m::register::psp::write(cur_thread.stack_top);
                }
            }
        } else {
            unsafe {
                cortex_m::register::psp::write(0x00000000);
            }
        }
    }

    #[task(binds = SVCall, resources = [rtos])]
    fn svcall(cx: svcall::Context) {
        hprintln!("svcall").unwrap();
        // Handle incoming RTOS commands.
        let mut svc_code: u32 = 0;
        unsafe {
            asm!("tst lr, #4
                  ite eq
                  moveq r0, r1
                  movne r0, r2
                  mrs r0, msp
                  mrs r0, psp
                  ldr r0, [r0, #24]
                  ldrb r0, [r0, #-2]",
                  out("r0") svc_code,
            );
        }
        match svc_code {
            1 => {
                // Exit thread.
                cx.resources.rtos.need_reschedule = true;
            },
            2 => {
                // Yield thread.
                cx.resources.rtos.need_reschedule = true;
            },
            3 => {
                // Sleep thread.
                cx.resources.rtos.need_reschedule = true;
            },
            4 => {
                // Semaphore get.
                cx.resources.rtos.need_reschedule = true;
            },
            5 => {
                // Semaphore put.
                cx.resources.rtos.need_reschedule = true;
            },
            _ => {
                unreachable!();
            }
        }

        if cx.resources.rtos.need_reschedule {
            cortex_m::peripheral::SCB::set_pendsv();
        }
    }

    #[idle(resources = [rtos])]
    fn idle(mut cx: idle::Context) -> ! {
        hprintln!("idle").unwrap();

        loop {
            cortex_m::asm::wfi();
        }
    }

    extern "C" {
        fn QEI0();
    }
};
