        .section .data
input_string:   .asciz "Hello world!"

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        
        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string

        # Your code here!
        #preload useful constants
        li t1, 'a' 
        li t2, 'z'
        li t3, 32
loop:
        #load current byte
        lb t0, 0(a0)

        blt t0, t1, skip_convert

        bgt t0, t2, skip_convert

        addi t0, t0, -32

        sb t0, 0(a0)

skip_convert:
        addi a0, a0, 1
        j loop

done:  
        #when finished, jump to the end
end_program:
        # jump here when you're done
        j end_program

