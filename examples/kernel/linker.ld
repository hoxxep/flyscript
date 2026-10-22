/* The kernel's image: loaded where QEMU's `virt` board puts RAM, its memory after it. */
ENTRY(_start)
SECTIONS
{
  . = 0x40080000;
  .text : { *(.text.boot) *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
  .data : { *(.data .data.*) }
  .bss (NOLOAD) : {
    . = ALIGN(16);
    __bss_start = .;
    *(.bss .bss.* COMMON)
    . = ALIGN(16);
    __bss_end = .;
  }
  . = ALIGN(16);
  . += 0x10000;
  __stack_top = .;
  . = ALIGN(4096);
  __heap_start = .;
  __heap_end = 0x48000000;
}
