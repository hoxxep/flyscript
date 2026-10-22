// The kernel's entry on QEMU's `virt` board: set up what C code needs, then run `kmain`.
.section .text.boot
.global _start
_start:
  // Floating point and SIMD on: compiled code and fiber switches use their registers.
  mov x0, #(3 << 20)
  msr cpacr_el1, x0
  isb
  ldr x0, =__stack_top
  mov sp, x0
  // Zero what the program expects zeroed.
  ldr x0, =__bss_start
  ldr x1, =__bss_end
1:
  cmp x0, x1
  b.hs 2f
  str xzr, [x0], #8
  b 1b
2:
  bl kmain
  bl powerOff

.text
// Ends the run: semihosting's SYS_EXIT, which QEMU run with `-semihosting` exits on, with the
// status in `x0`.
.global exitWith
exitWith:
  adr x1, exit_block
  str x0, [x1, #8]
  mov x0, #0x18
  hlt #0xf000
3:
  wfe
  b 3b
.global powerOff
powerOff:
  mov x0, #0
  b exitWith

.data
.balign 8
// ADP_Stopped_ApplicationExit, and the status.
exit_block:
  .quad 0x20026
  .quad 0

// Turns translation on with the page table at `x0`: memory attribute 0 is device memory, 1 normal
// cached memory; 39-bit addresses from TTBR0 in 4 KB pages; caches on.
.global mmuOn
mmuOn:
  ldr x1, =0xff00
  msr mair_el1, x1
  ldr x1, =(25 | (1 << 8) | (1 << 10) | (3 << 12) | (1 << 23) | (1 << 32))
  msr tcr_el1, x1
  msr ttbr0_el1, x0
  isb
  tlbi vmalle1
  dsb ish
  isb
  mrs x1, sctlr_el1
  orr x1, x1, #(1 << 0)
  orr x1, x1, #(1 << 2)
  orr x1, x1, #(1 << 12)
  msr sctlr_el1, x1
  isb
  ret

// Where the kernel's memory begins and ends.
.global heapStart
heapStart:
  ldr x0, =__heap_start
  ret
.global heapEnd
heapEnd:
  ldr x0, =__heap_end
  ret
