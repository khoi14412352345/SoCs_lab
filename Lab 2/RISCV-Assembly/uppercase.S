        .section .data
input_string:   .asciz "yes sir"

        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string

        # preload useful constants
        li t1, 'a'
        li t2, 'z'
        li t3, 32         

loop:
        lb t0, 0(a0)       # load current byte

        beq t0, x0, done   # if t0 == 0 => end of string -> done

        blt t0, t1, skip_convert
        bgt t0, t2, skip_convert

        addi t0, t0, -32   # make lowercase -> uppercase
        sb   t0, 0(a0)

skip_convert:
        addi a0, a0, 1
        j loop

done:
end_program:
        j end_program      # spin forever
