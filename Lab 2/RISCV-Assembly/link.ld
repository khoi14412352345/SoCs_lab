SECTIONS
{
  /* Start everything in RAM at 0x80000000, which is where Spike maps DRAM */
  . = 0x80000000;

  .text : {
    *(.text*)
    *(.rodata*)
  }

  .data : {
    *(.data*)
    *(.sdata*)
  }

  .bss : {
    *(.bss*)
    *(.sbss*)
    *(COMMON)
  }
}
