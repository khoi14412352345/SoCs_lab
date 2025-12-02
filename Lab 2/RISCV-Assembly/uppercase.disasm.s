
uppercase.bin:     file format elf32-littleriscv


Disassembly of section .text:

80000000 <_start>:
80000000:	00000517          	auipc	a0,0x0
80000004:	10050513          	addi	a0,a0,256 # 80000100 <input_string>
80000008:	06100313          	li	t1,97
8000000c:	07a00393          	li	t2,122
80000010:	02000e13          	li	t3,32

80000014 <loop>:
80000014:	00050283          	lb	t0,0(a0)
80000018:	00028e63          	beqz	t0,80000034 <done>
8000001c:	0062c863          	blt	t0,t1,8000002c <skip_convert>
80000020:	0053c663          	blt	t2,t0,8000002c <skip_convert>
80000024:	fe028293          	addi	t0,t0,-32
80000028:	00550023          	sb	t0,0(a0)

8000002c <skip_convert>:
8000002c:	00150513          	addi	a0,a0,1
80000030:	fe5ff06f          	j	80000014 <loop>

80000034 <done>:
80000034:	0000006f          	j	80000034 <done>
