use opcode::*;

mod opcode;

fn main() {
    let opcode = decode(0xA9);
    println!("{:?}", opcode);
}

const MEMORY_CPU_RAM: usize = 0x0000;
const MEMORY_IO_REGISTERS: usize = 0x2000;
const MEMORY_EXPANSION_ROM: usize = 0x4020;
const MEMORY_SAVE_RAM: usize = 0x6000;
const MEMORY_RPG_ROM: usize = 0x8000;
const MEMORY_MAX: usize = 0x10000;
const MEMORY_STACK: usize = 0x0100;
const MEMORY_NMI: usize = 0xFFFA;
const MEMORY_RESET: usize = 0xFFFC;
const MEMORY_IRQ_BRK: usize = 0xFFFE;

const FLAG_CARRY: u8 = 1 << 0;
const FLAG_ZERO: u8 = 1 << 1;
const FLAG_INTERRUPT_DISABLE: u8 = 1 << 2;
const FLAG_DECIMAL_MODE: u8 = 1 << 3;
const FLAG_BREAK: u8 = 1 << 4;
const FLAG_EMPTY: u8 = 1 << 5;
const FLAG_OVERFLOW: u8 = 1 << 6;
const FLAG_NEGATIVE: u8 = 1 << 7;

const BIT0: u8 = 1 << 0;
const BIT1: u8 = 1 << 1;
const BIT2: u8 = 1 << 2;
const BIT3: u8 = 1 << 3;
const BIT4: u8 = 1 << 4;
const BIT5: u8 = 1 << 5;
const BIT6: u8 = 1 << 6;
const BIT7: u8 = 1 << 7;

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: u8,
    pub program_counter: u16,
    pub stack_pointer: u8,
    memory: [u8; MEMORY_MAX],
}

impl CPU {
    #[inline]
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: 0,
            program_counter: 0,
            stack_pointer: 0,
            memory: [0x00; MEMORY_MAX],
        }
    }
}

impl CPU {
    #[inline]
    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    #[inline]
    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos.wrapping_add(1)) as u16;
        (hi << 8) | lo
    }

    #[inline]
    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }

    #[inline]
    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0x00ff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos.wrapping_add(1), hi);
    }

    #[inline]
    fn push(&mut self, data: u8) {
        self.mem_write(MEMORY_STACK as u16 | self.stack_pointer as u16, data);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    #[inline]
    fn push_u16(&mut self, data: u16) {
        self.push((data >> 8) as u8);
        self.push(data as u8);
    }

    #[inline]
    fn pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read(MEMORY_STACK as u16 | self.stack_pointer as u16)
    }

    #[inline]
    fn pop_u16(&mut self) -> u16 {
        let lo = self.pop() as u16;
        let hi = self.pop() as u16;
        (hi << 8) | lo
    }

    #[inline]
    fn load(&mut self, program: Vec<u8>) {
        self.memory[MEMORY_RPG_ROM..(MEMORY_RPG_ROM + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(MEMORY_RESET as u16, MEMORY_RPG_ROM as u16);
    }

    #[inline]
    fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.status = 0;
        self.stack_pointer = 0xFF;
        self.program_counter = self.mem_read_u16(MEMORY_RESET as u16);
    }
}

impl CPU {
    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::Indirect => self.mem_read_u16(self.mem_read_u16(self.program_counter)),
            AddressingMode::ZeroPageX => self
                .mem_read(self.program_counter)
                .wrapping_add(self.register_x) as u16,
            AddressingMode::ZeroPageY => self
                .mem_read(self.program_counter)
                .wrapping_add(self.register_y) as u16,
            AddressingMode::AbsoluteX => self
                .mem_read_u16(self.program_counter)
                .wrapping_add(self.register_x as u16),
            AddressingMode::AbsoluteY => self
                .mem_read_u16(self.program_counter)
                .wrapping_add(self.register_y as u16),
            AddressingMode::IndirectX => {
                let base = self.mem_read(self.program_counter);
                let ptr = base.wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16) as u16;
                let hi = self.mem_read(ptr.wrapping_add(1) as u16) as u16;
                (hi << 8) | lo
            }
            AddressingMode::IndirectY => {
                let base = self.mem_read(self.program_counter);
                let lo = self.mem_read(base as u16) as u16;
                let hi = self.mem_read(base.wrapping_add(1) as u16) as u16;
                ((hi << 8) | lo).wrapping_add(self.register_y as u16)
            }
            AddressingMode::Relative => {
                let base = self.mem_read(self.program_counter);
                ((base as i8) as i32 + self.program_counter as i32) as u16
            }
            AddressingMode::Implied => unreachable!(),
            AddressingMode::Accumulator => unreachable!(),
        }
    }

    fn run(&mut self) {
        loop {
            let binary = self.mem_read(self.program_counter);
            self.program_counter += 1;

            let opcode = decode(binary);
            match opcode.instruction {
                Instruction::ADC => self.adc(&opcode.addressing_mode),
                Instruction::AND => self.and(&opcode.addressing_mode),
                Instruction::ASL => self.asl(&opcode.addressing_mode),
                Instruction::BCC => self.bcc(&opcode.addressing_mode),
                Instruction::BCS => self.bcs(&opcode.addressing_mode),
                Instruction::BEQ => self.beq(&opcode.addressing_mode),
                Instruction::BIT => self.bit(&opcode.addressing_mode),
                Instruction::BMI => self.bmi(&opcode.addressing_mode),
                Instruction::BNE => self.bne(&opcode.addressing_mode),
                Instruction::BPL => self.bpl(&opcode.addressing_mode),
                Instruction::BRK => {
                    self.brk(&opcode.addressing_mode);
                    break;
                }
                Instruction::BVC => self.bvc(&opcode.addressing_mode),
                Instruction::BVS => self.bvs(&opcode.addressing_mode),
                Instruction::CLC => self.clc(&opcode.addressing_mode),
                Instruction::CLD => self.cld(&opcode.addressing_mode),
                Instruction::CLI => self.cli(&opcode.addressing_mode),
                Instruction::CLV => self.clv(&opcode.addressing_mode),
                Instruction::CMP => self.cmp(&opcode.addressing_mode),
                Instruction::CPX => self.cpx(&opcode.addressing_mode),
                Instruction::CPY => self.cpy(&opcode.addressing_mode),
                Instruction::DEC => self.dec(&opcode.addressing_mode),
                Instruction::DEX => self.dex(&opcode.addressing_mode),
                Instruction::DEY => self.dey(&opcode.addressing_mode),
                Instruction::EOR => self.eor(&opcode.addressing_mode),
                Instruction::INC => self.inc(&opcode.addressing_mode),
                Instruction::INX => self.inx(&opcode.addressing_mode),
                Instruction::INY => self.iny(&opcode.addressing_mode),
                Instruction::JMP => {
                    self.jmp(&opcode.addressing_mode);
                    continue;
                }
                Instruction::JSR => todo!(),
                Instruction::LDA => self.lda(&opcode.addressing_mode),
                Instruction::LDX => self.ldx(&opcode.addressing_mode),
                Instruction::LDY => self.ldy(&opcode.addressing_mode),
                Instruction::LSR => self.lsr(&opcode.addressing_mode),
                Instruction::NOP => self.nop(&opcode.addressing_mode),
                Instruction::ORA => self.ora(&opcode.addressing_mode),
                Instruction::PHA => todo!(),
                Instruction::PHP => todo!(),
                Instruction::PLA => todo!(),
                Instruction::PLP => todo!(),
                Instruction::ROL => self.rol(&opcode.addressing_mode),
                Instruction::ROR => self.ror(&opcode.addressing_mode),
                Instruction::RTI => todo!(),
                Instruction::RTS => todo!(),
                Instruction::SBC => self.sbc(&opcode.addressing_mode),
                Instruction::SEC => self.sec(&opcode.addressing_mode),
                Instruction::SED => self.sed(&opcode.addressing_mode),
                Instruction::SEI => self.sei(&opcode.addressing_mode),
                Instruction::STA => self.sta(&opcode.addressing_mode),
                Instruction::STX => self.stx(&opcode.addressing_mode),
                Instruction::STY => self.sty(&opcode.addressing_mode),
                Instruction::TAX => self.tax(&opcode.addressing_mode),
                Instruction::TAY => self.tay(&opcode.addressing_mode),
                Instruction::TSX => todo!(),
                Instruction::TXA => self.txa(&opcode.addressing_mode),
                Instruction::TXS => todo!(),
                Instruction::TYA => self.tya(&opcode.addressing_mode),
            }
            self.program_counter += opcode.bytes as u16 - 1;
        }
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let (rhs, carry_flag1) = value.overflowing_add(self.status & FLAG_CARRY);
        let (sum, carry_flag2) = self.register_a.overflowing_add(rhs);
        self.set_flag_overflow(
            (self.register_a & BIT7 == value & BIT7) && (value & BIT7 != sum & BIT7),
        );
        self.register_a = sum;
        self.set_flag_carry(carry_flag1 || carry_flag2);
        self.set_flag_zero(self.register_a.is_zero());
        self.set_flag_negative(self.register_a.is_negative());
    }

    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a &= value;
        self.set_flag_zero(self.register_a.is_zero());
        self.set_flag_negative(self.register_a.is_negative());
    }

    fn asl(&mut self, mode: &AddressingMode) {
        if mode == &AddressingMode::Accumulator {
            let (mul, carry) = self.register_a.overflowing_mul(2);
            self.register_a = mul;
            self.set_flag_carry(carry);
            self.set_flag_zero(self.register_a.is_zero());
            self.set_flag_negative(self.register_a.is_negative());
        } else {
            let addr = self.get_operand_address(mode);
            let value = self.mem_read(addr);
            let (mul, carry) = value.overflowing_mul(2);
            self.mem_write(addr, mul);
            self.set_flag_carry(carry);
            self.set_flag_zero(mul.is_zero());
            self.set_flag_negative(mul.is_negative());
        }
    }

    fn bcc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        if self.status & FLAG_CARRY == 0 {
            self.program_counter = addr;
        }
    }

    fn bcs(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        if self.status & FLAG_CARRY != 0 {
            self.program_counter = addr;
        }
    }

    fn beq(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        if self.status & FLAG_ZERO != 0 {
            self.program_counter = addr;
        }
    }

    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let and = self.register_a & value;
        self.set_flag_zero(and.is_zero());
        self.set_flag_overflow(value & BIT6 != 0);
        self.set_flag_negative(value & BIT7 != 0);
    }

    fn bmi(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        if self.status & FLAG_NEGATIVE != 0 {
            self.program_counter = addr;
        }
    }

    fn bne(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        if self.status & FLAG_ZERO == 0 {
            self.program_counter = addr;
        }
    }

    fn bpl(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        if self.status & FLAG_NEGATIVE == 0 {
            self.program_counter = addr;
        }
    }

    fn brk(&mut self, mode: &AddressingMode) {
        self.program_counter = self.mem_read_u16(MEMORY_IRQ_BRK as u16);
        self.set_flag_break(true);
    }

    fn bvc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        if self.status & FLAG_OVERFLOW == 0 {
            self.program_counter = addr;
        }
    }

    fn bvs(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        if self.status & FLAG_OVERFLOW != 0 {
            self.program_counter = addr;
        }
    }

    fn clc(&mut self, mode: &AddressingMode) {
        self.set_flag_carry(false);
    }

    fn cld(&mut self, mode: &AddressingMode) {
        self.set_flag_decimal_mode(false);
    }

    fn cli(&mut self, mode: &AddressingMode) {
        self.set_flag_interrupt_disable(false);
    }

    fn clv(&mut self, mode: &AddressingMode) {
        self.set_flag_overflow(false);
    }

    fn cmp(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let sub = self.register_a.wrapping_sub(value);
        self.set_flag_carry(sub.is_positive_or_zero());
        self.set_flag_zero(sub.is_zero());
        self.set_flag_negative(sub.is_negative());
    }

    fn cpx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let sub = self.register_x.wrapping_sub(value);
        self.set_flag_carry(sub.is_positive_or_zero());
        self.set_flag_zero(sub.is_zero());
        self.set_flag_negative(sub.is_negative());
    }

    fn cpy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let sub = self.register_y.wrapping_sub(value);
        self.set_flag_carry(sub.is_positive_or_zero());
        self.set_flag_zero(sub.is_zero());
        self.set_flag_negative(sub.is_negative());
    }

    fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let sub = value.wrapping_sub(1);
        self.mem_write(addr, sub);
        self.set_flag_zero(sub.is_zero());
        self.set_flag_negative(sub.is_negative());
    }

    fn dex(&mut self, mode: &AddressingMode) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.set_flag_zero(self.register_x.is_zero());
        self.set_flag_negative(self.register_x.is_negative());
    }

    fn dey(&mut self, mode: &AddressingMode) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.set_flag_zero(self.register_y.is_zero());
        self.set_flag_negative(self.register_y.is_negative());
    }

    fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a ^= value;
        self.set_flag_zero(self.register_a.is_zero());
        self.set_flag_negative(self.register_a.is_negative());
    }

    fn inc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let add = value.wrapping_add(1);
        self.mem_write(addr, add);
        self.set_flag_zero(add.is_zero());
        self.set_flag_negative(add.is_negative());
    }

    fn inx(&mut self, mode: &AddressingMode) {
        self.register_x = self.register_x.wrapping_add(1);
        self.set_flag_zero(self.register_x.is_zero());
        self.set_flag_negative(self.register_x.is_negative());
    }

    fn iny(&mut self, mode: &AddressingMode) {
        self.register_y = self.register_y.wrapping_add(1);
        self.set_flag_zero(self.register_y.is_zero());
        self.set_flag_negative(self.register_y.is_negative());
    }

    fn jmp(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.program_counter = addr;
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a = value;
        self.set_flag_zero(self.register_a.is_zero());
        self.set_flag_negative(self.register_a.is_negative());
    }

    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_x = value;
        self.set_flag_zero(self.register_x.is_zero());
        self.set_flag_negative(self.register_x.is_negative());
    }

    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_y = value;
        self.set_flag_zero(self.register_y.is_zero());
        self.set_flag_negative(self.register_y.is_negative());
    }

    fn lsr(&mut self, mode: &AddressingMode) {
        if mode == &AddressingMode::Accumulator {
            let carry = self.register_a & BIT0 != 0;
            self.register_a >>= 1;
            self.set_flag_carry(carry);
            self.set_flag_zero(self.register_a.is_zero());
            self.set_flag_negative(self.register_a.is_negative());
        } else {
            let addr = self.get_operand_address(mode);
            let value = self.mem_read(addr);
            let carry = value & BIT0 != 0;
            let div = value >> 1;
            self.mem_write(addr, div);
            self.set_flag_carry(carry);
            self.set_flag_zero(div.is_zero());
            self.set_flag_negative(div.is_negative());
        }
    }

    fn nop(&mut self, mode: &AddressingMode) {
        // do nothing
    }

    fn ora(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a |= value;
        self.set_flag_zero(self.register_a.is_zero());
        self.set_flag_negative(self.register_a.is_negative());
    }

    fn rol(&mut self, mode: &AddressingMode) {
        if mode == &AddressingMode::Accumulator {
            let (mul, carry) = self.register_a.overflowing_mul(2);
            self.register_a = mul | (self.status & FLAG_CARRY);
            self.set_flag_carry(carry);
            self.set_flag_zero(self.register_a.is_zero());
            self.set_flag_negative(self.register_a.is_negative());
        } else {
            let addr = self.get_operand_address(mode);
            let value = self.mem_read(addr);
            let (mut mul, carry) = value.overflowing_mul(2);
            mul |= self.status & FLAG_CARRY;
            self.mem_write(addr, mul);
            self.set_flag_carry(carry);
            self.set_flag_zero(mul.is_zero());
            self.set_flag_negative(mul.is_negative());
        }
    }

    fn ror(&mut self, mode: &AddressingMode) {
        if mode == &AddressingMode::Accumulator {
            let carry = self.register_a & BIT0 != 0;
            self.register_a = (self.register_a >> 1) | ((self.status & FLAG_CARRY) << 7);
            self.set_flag_carry(carry);
            self.set_flag_zero(self.register_a.is_zero());
            self.set_flag_negative(self.register_a.is_negative());
        } else {
            let addr = self.get_operand_address(mode);
            let value = self.mem_read(addr);
            let carry = value & BIT0 != 0;
            let div = (value >> 1) | ((self.status & FLAG_CARRY) << 7);
            self.mem_write(addr, div);
            self.set_flag_carry(carry);
            self.set_flag_zero(div.is_zero());
            self.set_flag_negative(div.is_negative());
        }
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let (lhs, carry_flag1) = self.register_a.overflowing_sub(value);
        let (sub, carry_flag2) = lhs.overflowing_sub(0x01 - (self.status & FLAG_CARRY));
        self.set_flag_overflow(
            (self.register_a & BIT7 != value & BIT7) && (self.register_a & BIT7 != sub & BIT7),
        );
        self.register_a = sub;
        self.set_flag_carry(!carry_flag1 && !carry_flag2);
        self.set_flag_zero(self.register_a.is_zero());
        self.set_flag_negative(self.register_a.is_negative());
    }

    fn sec(&mut self, mode: &AddressingMode) {
        self.set_flag_carry(true);
    }

    fn sed(&mut self, mode: &AddressingMode) {
        self.set_flag_decimal_mode(true);
    }

    fn sei(&mut self, mode: &AddressingMode) {
        self.set_flag_interrupt_disable(true);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_x);
    }

    fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_y);
    }

    fn tax(&mut self, mode: &AddressingMode) {
        self.register_x = self.register_a;
        self.set_flag_zero(self.register_x.is_zero());
        self.set_flag_negative(self.register_x.is_negative());
    }

    fn tay(&mut self, mode: &AddressingMode) {
        self.register_y = self.register_a;
        self.set_flag_zero(self.register_y.is_zero());
        self.set_flag_negative(self.register_y.is_negative());
    }

    fn txa(&mut self, mode: &AddressingMode) {
        self.register_a = self.register_x;
        self.set_flag_zero(self.register_a.is_zero());
        self.set_flag_negative(self.register_a.is_negative());
    }

    fn tya(&mut self, mode: &AddressingMode) {
        self.register_a = self.register_y;
        self.set_flag_zero(self.register_a.is_zero());
        self.set_flag_negative(self.register_a.is_negative());
    }
}

impl CPU {
    #[inline]
    fn set_flag_carry(&mut self, flag: bool) {
        self.status = if flag {
            self.status | FLAG_CARRY
        } else {
            self.status & !FLAG_CARRY
        }
    }

    #[inline]
    fn set_flag_zero(&mut self, flag: bool) {
        self.status = if flag {
            self.status | FLAG_ZERO
        } else {
            self.status & !FLAG_ZERO
        }
    }

    #[inline]
    fn set_flag_interrupt_disable(&mut self, flag: bool) {
        self.status = if flag {
            self.status | FLAG_INTERRUPT_DISABLE
        } else {
            self.status & !FLAG_INTERRUPT_DISABLE
        }
    }

    #[inline]
    fn set_flag_decimal_mode(&mut self, flag: bool) {
        self.status = if flag {
            self.status | FLAG_DECIMAL_MODE
        } else {
            self.status & !FLAG_DECIMAL_MODE
        }
    }

    #[inline]
    fn set_flag_break(&mut self, flag: bool) {
        self.status = if flag {
            self.status | FLAG_BREAK
        } else {
            self.status & !FLAG_BREAK
        }
    }

    #[inline]
    fn set_flag_empty(&mut self, flag: bool) {
        self.status = if flag {
            self.status | FLAG_EMPTY
        } else {
            self.status & !FLAG_EMPTY
        }
    }

    #[inline]
    fn set_flag_overflow(&mut self, flag: bool) {
        self.status = if flag {
            self.status | FLAG_OVERFLOW
        } else {
            self.status & !FLAG_OVERFLOW
        }
    }

    #[inline]
    fn set_flag_negative(&mut self, flag: bool) {
        self.status = if flag {
            self.status | FLAG_NEGATIVE
        } else {
            self.status & !FLAG_NEGATIVE
        }
    }
}

trait BitCheck {
    fn is_zero(&self) -> bool;
    fn is_positive_or_zero(&self) -> bool;
    fn is_negative_or_zero(&self) -> bool;
    fn is_positive(&self) -> bool;
    fn is_negative(&self) -> bool;
}

impl BitCheck for u8 {
    // u8を符号つきとみなして判定する
    #[inline]
    fn is_zero(&self) -> bool {
        *self == 0
    }

    #[inline]
    fn is_positive_or_zero(&self) -> bool {
        self & BIT7 == 0
    }

    #[inline]
    fn is_negative_or_zero(&self) -> bool {
        (self & BIT7 != 0) || (*self == 0)
    }

    #[inline]
    fn is_positive(&self) -> bool {
        (self & BIT7 == 0) && (*self != 0)
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self & BIT7 != 0
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // #[test]
    // fn test_format_trace() {
    //     let mut bus = Bus::new(test_rom(), move |ppu: &NesPPU| {});
    //     bus.mem_write(100, 0xa2);
    //     bus.mem_write(101, 0x01);
    //     bus.mem_write(102, 0xca);
    //     bus.mem_write(103, 0x88);
    //     bus.mem_write(104, 0x00);

    //     let mut cpu = CPU::new(bus);
    //     cpu.program_counter = 0x64;
    //     cpu.register_a = 1;
    //     cpu.register_x = 2;
    //     cpu.register_y = 3;

    //     let mut result: Vec<String> = vec![];
    //     cpu.run_with_callback(|cpu| {
    //         result.push(trace(cpu));
    //     });

    //     assert_eq!(
    //         "0064  A2 01     LDX #$01                        A:01 X:02 Y:03 P:24 SP:FD",
    //         result[0]
    //     );
    //     assert_eq!(
    //         "0066  CA        DEX                             A:01 X:01 Y:03 P:24 SP:FD",
    //         result[1]
    //     );
    //     assert_eq!(
    //         "0067  88        DEY                             A:01 X:00 Y:03 P:26 SP:FD",
    //         result[2]
    //     );
    // }

    // #[test]
    // fn test_format_mem_access() {
    //     let mut bus = Bus::new(test_rom(), move |ppu: &NesPPU| {});
    //     // ORA ($33), Y
    //     bus.mem_write(100, 0x11);
    //     bus.mem_write(101, 0x33);

    //     // data
    //     bus.mem_write(0x33, 0x00);
    //     bus.mem_write(0x34, 0x04);

    //     // target cell
    //     bus.mem_write(0x0400, 0xAA);

    //     let mut cpu = CPU::new(bus);
    //     cpu.program_counter = 0x64;
    //     cpu.register_y = 0;

    //     let mut result: Vec<String> = vec![];
    //     cpu.run_with_callback(|cpu| {
    //         result.push(trace(cpu));
    //     });
    //     assert_eq!(
    //         "0064  11 33     ORA ($33),Y = 0400 @ 0400 = AA  A:00 X:00 Y:00 P:24 SP:FD",
    //         result[0]
    //     );
    // }

    // Instruction tests
    // use super::*;
    fn run<F>(program: Vec<u8>, f: F) -> CPU
    where
        F: Fn(&mut CPU),
    {
        let mut cpu = CPU::new();
        cpu.load(program);
        cpu.reset();
        f(&mut cpu);
        cpu.run();
        cpu
    }

    fn assert_status(cpu: &CPU, flags: u8) {
        assert_eq!(cpu.status, flags)
    }

    // LDA
    #[test]
    fn test_0xa9_lda_immidiate_load_data() {
        let cpu = run(vec![0xa9, 0x05, 0x00], |_| {});
        assert_eq!(cpu.register_a, 0x05);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let cpu = run(vec![0xa9, 0x00, 0x00], |_| {});
        assert_status(&cpu, FLAG_ZERO | FLAG_BREAK);
    }

    #[test]
    fn test_0xa9_lda_negative_flag() {
        let cpu = run(vec![0xa9, 0x80, 0x00], |_| {});
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    #[test]
    fn test_lda_from_memory_zero_page() {
        let cpu = run(vec![0xa5, 0x10, 0x00], |cpu| {
            cpu.mem_write(0x10, 0x55);
        });
        assert_eq!(cpu.register_a, 0x55 | FLAG_BREAK);
    }

    #[test]
    fn test_lda_from_memory_zero_page_x() {
        let cpu = run(vec![0xb5, 0x10, 0x00], |cpu| {
            cpu.mem_write(0x11, 0x56);
            cpu.register_x = 0x01;
        });
        assert_eq!(cpu.register_a, 0x56 | FLAG_BREAK);
    }

    #[test]
    fn test_lda_from_memory_absolute() {
        let cpu = run(vec![0xad, 0x10, 0xaa, 0x00], |cpu| {
            cpu.mem_write(0xAA10, 0x57);
        });
        assert_eq!(cpu.register_a, 0x57 | FLAG_BREAK);
    }

    #[test]
    fn test_lda_from_memory_absolute_x() {
        let cpu = run(vec![0xbd, 0x10, 0xaa, 0x00], |cpu| {
            cpu.mem_write(0xAA15, 0x58);
            cpu.register_x = 0x05;
        });
        assert_eq!(cpu.register_a, 0x58 | FLAG_BREAK);
    }

    #[test]
    fn test_lda_from_memory_absolute_y() {
        let cpu = run(vec![0xb9, 0x10, 0xaa, 0x00], |cpu| {
            cpu.mem_write(0xAA18, 0x59);
            cpu.register_y = 0x08;
        });
        assert_eq!(cpu.register_a, 0x59 | FLAG_BREAK);
    }

    #[test]
    fn test_lda_from_memory_indirect_x() {
        let cpu = run(vec![0xa1, 0x10, 0x00], |cpu| {
            cpu.mem_write_u16(0x18, 0xFF05);
            cpu.mem_write(0xFF05, 0x5A);
            cpu.register_x = 0x08;
        });
        assert_eq!(cpu.register_a, 0x5A | FLAG_BREAK);
    }

    #[test]
    fn test_lda_from_memory_indirect_y() {
        let cpu = run(vec![0xb1, 0x10, 0x00], |cpu| {
            cpu.mem_write_u16(0x10, 0xFF06);
            cpu.mem_write(0xFF09, 0x5B);
            cpu.register_y = 0x03;
        });
        assert_eq!(cpu.register_a, 0x5B | FLAG_BREAK);
    }

    // #[test]
    // fn test_5_ops_working_together() {
    //     let cpu = run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00], |_| {});
    //     assert_eq!(cpu.register_x, 0xc1);
    // }

    // STA
    #[test]
    fn test_sta_from_memory() {
        let cpu = run(vec![0x85, 0x10, 0x00], |cpu| {
            cpu.register_a = 0xBA;
        });
        assert_eq!(cpu.mem_read(0x10), 0xBA);
    }

    // ADC
    #[test]
    fn test_adc_no_carry() {
        let cpu = run(vec![0x69, 0x10, 0x00], |cpu| {
            cpu.register_a = 0x20;
        });
        assert_eq!(cpu.register_a, 0x30);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_adc_has_carry() {
        let cpu = run(vec![0x69, 0x10, 0x00], |cpu| {
            cpu.register_a = 0x20;
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_a, 0x31);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_adc_occur_carry() {
        let cpu = run(vec![0x69, 0x01, 0x00], |cpu| {
            cpu.register_a = 0xFF;
        });
        assert_eq!(cpu.register_a, 0x00);
        assert_status(&cpu, FLAG_CARRY | FLAG_ZERO | FLAG_BREAK);
    }

    #[test]
    fn test_adc_occur_overflow_plus() {
        let cpu = run(vec![0x69, 0x10, 0x00], |cpu| {
            cpu.register_a = 0x7F;
        });
        assert_eq!(cpu.register_a, 0x8F);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_OVERFLOW | FLAG_BREAK);
    }

    #[test]
    fn test_adc_occur_overflow_plus_with_carry() {
        let cpu = run(vec![0x69, 0x6F, 0x00], |cpu| {
            cpu.register_a = 0x10;
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_a, 0x80);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_OVERFLOW | FLAG_BREAK);
    }

    #[test]
    fn test_adc_occur_overflow_minus() {
        let cpu = run(vec![0x69, 0x81, 0x00], |cpu| {
            cpu.register_a = 0x81;
        });
        assert_eq!(cpu.register_a, 0x02);
        assert_status(&cpu, FLAG_OVERFLOW | FLAG_CARRY | FLAG_BREAK);
    }

    #[test]
    fn test_adc_occur_overflow_minus_with_carry() {
        let mut cpu = run(vec![0x69, 0x80, 0x00], |cpu| {
            cpu.register_a = 0x80;
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_a, 0x01);
        assert_status(&cpu, FLAG_OVERFLOW | FLAG_CARRY | FLAG_BREAK);
    }

    #[test]
    fn test_adc_no_overflow() {
        let cpu = run(vec![0x69, 0x7F, 0x00], |cpu| {
            cpu.register_a = 0x82;
        });
        assert_eq!(cpu.register_a, 0x01);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    // SBC
    #[test]
    fn test_sbc_no_carry() {
        let cpu = run(vec![0xe9, 0x10, 0x00], |cpu| {
            cpu.register_a = 0x20;
        });
        assert_eq!(cpu.register_a, 0x0F);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    #[test]
    fn test_sbc_has_carry() {
        let mut cpu = run(vec![0xe9, 0x10, 0x00], |cpu| {
            cpu.register_a = 0x20;
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_a, 0x10);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    #[test]
    fn test_sbc_occur_carry() {
        let cpu = run(vec![0xe9, 0x02, 0x00], |cpu| {
            cpu.register_a = 0x01;
        });
        assert_eq!(cpu.register_a, 0xFE);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    #[test]
    fn test_sbc_occur_overflow() {
        let cpu = run(vec![0xe9, 0x81, 0x00], |cpu| {
            cpu.register_a = 0x7F;
        });
        assert_eq!(cpu.register_a, 0xFD);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_OVERFLOW | FLAG_BREAK);
    }

    #[test]
    fn test_sbc_occur_overflow_with_carry() {
        let cpu = run(vec![0xe9, 0x81, 0x00], |cpu| {
            cpu.register_a = 0x7F;
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_a, 0xFE);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_OVERFLOW | FLAG_BREAK);
    }

    #[test]
    fn test_sbc_no_overflow() {
        let cpu = run(vec![0xe9, 0x7F, 0x00], |cpu| {
            cpu.register_a = 0x7E;
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_a, 0xFF);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    // AND
    #[test]
    fn test_and() {
        let cpu = run(vec![0x29, 0x0C, 0x00], |cpu| {
            cpu.register_a = 0x0A;
        });
        assert_eq!(cpu.register_a, 0x08);
        assert_status(&cpu, FLAG_BREAK);
    }

    // EOR
    #[test]
    fn test_eor() {
        let cpu = run(vec![0x49, 0x0C, 0x00], |cpu| {
            cpu.register_a = 0x0A;
        });
        assert_eq!(cpu.register_a, 0x06);
        assert_status(&cpu, FLAG_BREAK);
    }

    // ORA
    #[test]
    fn test_ora() {
        let cpu = run(vec![0x09, 0x0C, 0x00], |cpu| {
            cpu.register_a = 0x0A;
        });
        assert_eq!(cpu.register_a, 0x0E);
        assert_status(&cpu, FLAG_BREAK);
    }

    // ASL
    #[test]
    fn test_asl_a() {
        let cpu = run(vec![0x0A, 0x00], |cpu| {
            cpu.register_a = 0x03;
        });
        assert_eq!(cpu.register_a, 0x03 * 2);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_asl_zero_page() {
        let cpu = run(vec![0x06, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x03);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x03 * 2);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_asl_a_occur_carry() {
        let cpu = run(vec![0x0A, 0x00], |cpu| {
            cpu.register_a = 0x81;
        });
        assert_eq!(cpu.register_a, 0x02);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    #[test]
    fn test_asl_zero_page_occur_carry() {
        let cpu = run(vec![0x06, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x81);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x02);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    // LSR
    #[test]
    fn test_lsr_a() {
        let cpu = run(vec![0x4A, 0x00], |cpu| {
            cpu.register_a = 0x02;
        });
        assert_eq!(cpu.register_a, 0x01);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_lsr_zero_page() {
        let cpu = run(vec![0x46, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x02);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x01);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_lsr_zero_page_zero_flag() {
        let cpu = run(vec![0x46, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x01);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x00);
        assert_status(&cpu, FLAG_ZERO | FLAG_CARRY | FLAG_BREAK);
    }

    #[test]
    fn test_lsr_a_occur_carry() {
        let cpu = run(vec![0x4A, 0x00], |cpu| {
            cpu.register_a = 0x03;
        });
        assert_eq!(cpu.register_a, 0x01);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    #[test]
    fn test_lsr_zero_page_occur_carry() {
        let cpu = run(vec![0x46, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x03);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x01);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    // ROL
    #[test]
    fn test_rol_a() {
        let cpu = run(vec![0x2A, 0x00], |cpu| {
            cpu.register_a = 0x03;
        });
        assert_eq!(cpu.register_a, 0x03 * 2);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_rol_zero_page() {
        let cpu = run(vec![0x26, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x03);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x03 * 2);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_rol_a_with_carry() {
        let cpu = run(vec![0x2A, 0x00], |cpu| {
            cpu.register_a = 0x03;
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_a, 0x03 * 2 + 1);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_rol_zero_page_with_carry() {
        let cpu = run(vec![0x26, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x03);
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.mem_read(0x0001), 0x03 * 2 + 1);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_rol_a_zero_with_carry() {
        let cpu = run(vec![0x2A, 0x00], |cpu| {
            cpu.register_a = 0x00;
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_a, 0x01);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_rol_zero_page_zero_with_carry() {
        let cpu = run(vec![0x26, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x00);
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.mem_read(0x0001), 0x01);
        assert_status(&cpu, FLAG_BREAK);
    }

    // ROR
    #[test]
    fn test_ror_a() {
        let cpu = run(vec![0x6A, 0x00], |cpu| {
            cpu.register_a = 0x02;
        });
        assert_eq!(cpu.register_a, 0x01);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_ror_zero_page() {
        let cpu = run(vec![0x66, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x02);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x01);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_ror_a_occur_carry() {
        let cpu = run(vec![0x6A, 0x00], |cpu| {
            cpu.register_a = 0x03;
        });
        assert_eq!(cpu.register_a, 0x01);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    #[test]
    fn test_ror_zero_page_occur_carry() {
        let cpu = run(vec![0x66, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x03);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x01);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    #[test]
    fn test_ror_a_with_carry() {
        let cpu = run(vec![0x6A, 0x00], |cpu| {
            cpu.register_a = 0x03;
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_a, 0x81);
        assert_status(&cpu, FLAG_CARRY | FLAG_NEGATIVE | FLAG_BREAK);
    }

    #[test]
    fn test_ror_zero_page_with_carry() {
        let cpu = run(vec![0x66, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x03);
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.mem_read(0x0001), 0x81);
        assert_status(&cpu, FLAG_CARRY | FLAG_NEGATIVE | FLAG_BREAK);
    }

    #[test]
    fn test_ror_a_zero_with_carry() {
        let cpu = run(vec![0x6A, 0x00], |cpu| {
            cpu.register_a = 0x00;
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_a, 0x80);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    #[test]
    fn test_ror_zero_page_zero_with_carry() {
        let cpu = run(vec![0x66, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x00);
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.mem_read(0x0001), 0x80);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    // BCC
    #[test]
    fn test_bcc() {
        let cpu = run(vec![0x90, 0x02, 0x00, 0x00, 0xe8, 0x00], |_| {});
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8006)
    }

    #[test]
    fn test_bcc_with_carry() {
        let cpu = run(vec![0x90, 0x02, 0x00, 0x00, 0xe8, 0x00], |cpu| {
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_x, 0x00);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8003)
    }

    #[test]
    fn test_bcc_negative() {
        let cpu = run(vec![0x90, 0xfc, 0x00], |cpu| {
            cpu.mem_write(0x7FFF, 0x00);
            cpu.mem_write(0x7FFE, 0xe8);
        });
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8000)
    }

    // BCS
    #[test]
    fn test_bcs() {
        let cpu = run(vec![0xb0, 0x02, 0x00, 0x00, 0xe8, 0x00], |_| {});
        assert_eq!(cpu.register_x, 0x00);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8003)
    }

    #[test]
    fn test_bcs_with_carry() {
        let cpu = run(vec![0xb0, 0x02, 0x00, 0x00, 0xe8, 0x00], |cpu| {
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8006)
    }

    #[test]
    fn test_bcs_negative() {
        let cpu = run(vec![0xb0, 0xfc, 0x00], |cpu| {
            cpu.mem_write(0x7FFF, 0x00);
            cpu.mem_write(0x7FFE, 0xe8);
            cpu.status = FLAG_CARRY;
        });
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8000)
    }

    // BEQ
    #[test]
    fn test_beq() {
        let cpu = run(vec![0xF0, 0x02, 0x00, 0x00, 0xe8, 0x00], |cpu| {});
        assert_eq!(cpu.register_x, 0x00);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8003)
    }

    #[test]
    fn test_beq_with_zero_flag() {
        let cpu = run(vec![0xF0, 0x02, 0x00, 0x00, 0xe8, 0x00], |cpu| {
            cpu.status = FLAG_ZERO;
        });
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_BREAK); // ZEROはINXで落ちる
        assert_eq!(cpu.program_counter, 0x8006)
    }

    // BNE
    #[test]
    fn test_bne() {
        let cpu = run(vec![0xD0, 0x02, 0x00, 0x00, 0xe8, 0x00], |_| {});
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8006)
    }

    #[test]
    fn test_bne_with_zero_flag() {
        let cpu = run(vec![0xD0, 0x02, 0x00, 0x00, 0xe8, 0x00], |cpu| {
            cpu.status = FLAG_ZERO;
        });
        assert_eq!(cpu.register_x, 0x00);
        assert_status(&cpu, FLAG_ZERO | FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8003)
    }

    // BIT
    #[test]
    fn test_bit() {
        let cpu = run(vec![0x24, 0x00, 0x00], |cpu| {
            cpu.register_a = 0x00;
            cpu.mem_write(0x0000, 0x00);
        });
        assert_status(&cpu, FLAG_ZERO | FLAG_BREAK);
    }

    #[test]
    fn test_bit_negative_flag() {
        let cpu = run(vec![0x24, 0x00, 0x00], |cpu| {
            cpu.register_a = 0x00;
            cpu.mem_write(0x0000, 0x80);
        });
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_ZERO | FLAG_BREAK);
    }

    #[test]
    fn test_bit_overflow_flag() {
        let cpu = run(vec![0x24, 0x00, 0x00], |cpu| {
            cpu.register_a = 0x40;
            cpu.mem_write(0x0000, 0x40);
        });
        assert_status(&cpu, FLAG_OVERFLOW | FLAG_BREAK);
    }

    // BMI
    #[test]
    fn test_bmi() {
        let cpu = run(vec![0x30, 0x02, 0x00, 0x00, 0xe8, 0x00], |_| {});
        assert_eq!(cpu.register_x, 0x00);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8003)
    }

    #[test]
    fn test_bmi_with_negative_flag() {
        let cpu = run(vec![0x30, 0x02, 0x00, 0x00, 0xe8, 0x00], |cpu| {
            cpu.status = FLAG_NEGATIVE;
        });
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_BREAK); //INXしてるからnegativeが落ちる
        assert_eq!(cpu.program_counter, 0x8006)
    }

    // BPL
    #[test]
    fn test_bpl() {
        let cpu = run(vec![0x10, 0x02, 0x00, 0x00, 0xe8, 0x00], |_| {});
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8006)
    }

    #[test]
    fn test_bpl_with_negative_flag() {
        let cpu = run(vec![0x10, 0x02, 0x00, 0x00, 0xe8, 0x00], |cpu| {
            cpu.status = FLAG_NEGATIVE;
        });
        assert_eq!(cpu.register_x, 0x00);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8003)
    }

    // BVC
    #[test]
    fn test_bvc() {
        let cpu = run(vec![0x50, 0x02, 0x00, 0x00, 0xe8, 0x00], |_| {});
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8006)
    }

    #[test]
    fn test_bvc_with_overflow_flag() {
        let cpu = run(vec![0x50, 0x02, 0x00, 0x00, 0xe8, 0x00], |cpu| {
            cpu.status = FLAG_OVERFLOW;
        });
        assert_eq!(cpu.register_x, 0x00);
        assert_status(&cpu, FLAG_OVERFLOW | FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8003)
    }

    // BVS
    #[test]
    fn test_bvs() {
        let cpu = run(vec![0x70, 0x02, 0x00, 0x00, 0xe8, 0x00], |_| {});
        assert_eq!(cpu.register_x, 0x00);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8003);
    }

    #[test]
    fn test_bvs_with_overflow_flag() {
        let cpu = run(vec![0x70, 0x02, 0x00, 0x00, 0xe8, 0x00], |cpu| {
            cpu.status = FLAG_OVERFLOW;
        });
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_OVERFLOW | FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x8006)
    }

    // CLC
    #[test]
    fn test_clc() {
        let cpu = run(vec![0x18, 0x00], |cpu| {
            cpu.status = FLAG_CARRY | FLAG_NEGATIVE;
        });
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    // SEC
    #[test]
    fn test_sec() {
        let cpu = run(vec![0x38, 0x00], |cpu| {
            cpu.status = FLAG_NEGATIVE;
        });
        assert_status(&cpu, FLAG_CARRY | FLAG_NEGATIVE | FLAG_BREAK);
    }

    // CLD
    #[test]
    fn test_cld() {
        let cpu = run(vec![0xd8, 0x00], |cpu| {
            cpu.status = FLAG_DECIMAL_MODE | FLAG_NEGATIVE;
        });
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    // SED
    #[test]
    fn test_sed() {
        let cpu = run(vec![0xf8, 0x00], |cpu| {
            cpu.status = FLAG_NEGATIVE;
        });
        assert_status(&cpu, FLAG_DECIMAL_MODE | FLAG_NEGATIVE | FLAG_BREAK);
    }

    // CLI
    #[test]
    fn test_cli() {
        let cpu = run(vec![0x58, 0x00], |cpu| {
            cpu.status = FLAG_INTERRUPT_DISABLE | FLAG_NEGATIVE;
        });
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    // SEI
    #[test]
    fn test_sei() {
        let cpu = run(vec![0x78, 0x00], |cpu| {
            cpu.status = FLAG_NEGATIVE;
        });
        assert_status(&cpu, FLAG_INTERRUPT_DISABLE | FLAG_NEGATIVE | FLAG_BREAK);
    }

    // CLV
    #[test]
    fn test_clv() {
        let cpu = run(vec![0xb8, 0x00], |cpu| {
            cpu.status = FLAG_OVERFLOW | FLAG_NEGATIVE;
        });
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    // CMP
    #[test]
    fn test_cmp() {
        let cpu = run(vec![0xC9, 0x01, 0x00], |cpu| {
            cpu.register_a = 0x02;
        });
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    #[test]
    fn test_cmp_eq() {
        let cpu = run(vec![0xC9, 0x02, 0x00], |cpu| {
            cpu.register_a = 0x02;
        });
        assert_status(&cpu, FLAG_CARRY | FLAG_ZERO | FLAG_BREAK);
    }

    #[test]
    fn test_cmp_negative() {
        let cpu = run(vec![0xC9, 0x03, 0x00], |cpu| {
            cpu.register_a = 0x02;
        });
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    // CPX
    #[test]
    fn test_cpx() {
        let cpu = run(vec![0xe0, 0x01, 0x00], |cpu| {
            cpu.register_x = 0x02;
        });
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    // CPY
    #[test]
    fn test_cpy() {
        let cpu = run(vec![0xc0, 0x01, 0x00], |cpu| {
            cpu.register_y = 0x02;
        });
        assert_status(&cpu, FLAG_CARRY | FLAG_BREAK);
    }

    // DEC
    #[test]
    fn test_dec() {
        let cpu = run(vec![0xc6, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x05);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x04);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_dec_overflow() {
        let cpu = run(vec![0xc6, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x00);
        });
        assert_eq!(cpu.mem_read(0x0001), 0xFF);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    // DEX
    #[test]
    fn test_dex() {
        let cpu = run(vec![0xca, 0x00], |cpu| {
            cpu.register_x = 0x05;
        });
        assert_eq!(cpu.register_x, 0x04);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_dex_overflow() {
        let cpu = run(vec![0xca, 0x00], |cpu| {
            cpu.register_x = 0x00;
        });
        assert_eq!(cpu.register_x, 0xFF);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    // DEY
    #[test]
    fn test_dey() {
        let cpu = run(vec![0x88, 0x00], |cpu| {
            cpu.register_y = 0x05;
        });
        assert_eq!(cpu.register_y, 0x04);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_dey_overflow() {
        let cpu = run(vec![0x88, 0x00], |cpu| {
            cpu.register_y = 0x00;
        });
        assert_eq!(cpu.register_y, 0xFF);
        assert_status(&cpu, FLAG_NEGATIVE | FLAG_BREAK);
    }

    // INC
    #[test]
    fn test_inc() {
        let cpu = run(vec![0xe6, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0x05);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x06);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_inc_overflow() {
        let cpu = run(vec![0xe6, 0x01, 0x00], |cpu| {
            cpu.mem_write(0x0001, 0xFF);
        });
        assert_eq!(cpu.mem_read(0x0001), 0x00);
        assert_status(&cpu, FLAG_ZERO | FLAG_BREAK);
    }

    // INX
    #[test]
    fn test_inx() {
        let cpu = run(vec![0xe8, 0x00], |cpu| {
            cpu.register_x = 0x05;
        });
        assert_eq!(cpu.register_x, 0x06);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_inx_overflow() {
        let cpu = run(vec![0xe8, 0x00], |cpu| {
            cpu.register_x = 0xFF;
        });
        assert_eq!(cpu.register_x, 0x00);
        assert_status(&cpu, FLAG_ZERO | FLAG_BREAK);
    }

    // INY
    #[test]
    fn test_iny() {
        let cpu = run(vec![0xc8, 0x00], |cpu| {
            cpu.register_y = 0x05;
        });
        assert_eq!(cpu.register_y, 0x06);
        assert_status(&cpu, FLAG_BREAK);
    }

    #[test]
    fn test_iny_overflow() {
        let cpu = run(vec![0xc8, 0x00], |cpu| {
            cpu.register_y = 0xFF;
        });
        assert_eq!(cpu.register_y, 0x00);
        assert_status(&cpu, FLAG_ZERO | FLAG_BREAK);
    }

    // JMP
    #[test]
    fn test_jmp() {
        let cpu = run(vec![0x4c, 0x30, 0x40, 0x00], |cpu| {
            cpu.mem_write(0x4030, 0xe8);
            cpu.mem_write(0x4031, 0x00);
        });
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x4032);
    }

    #[test]
    fn test_jmp_indirect() {
        let cpu = run(vec![0x6c, 0x30, 0x40, 0x00], |cpu| {
            cpu.mem_write(0x4030, 0x01);
            cpu.mem_write(0x4031, 0x02);

            cpu.mem_write(0x0201, 0xe8);
            cpu.mem_write(0x0202, 0x00);
        });
        assert_eq!(cpu.register_x, 0x01);
        assert_status(&cpu, FLAG_BREAK);
        assert_eq!(cpu.program_counter, 0x0203);
    }

    // // JSR
    // #[test]
    // fn test_jsr() {
    //     let cpu = run(vec![0x20, 0x30, 0x40, 0x00], |cpu| {
    //         cpu.mem_write(0x4030, 0xe8);
    //         cpu.mem_write(0x4031, 0x00);
    //     });
    //     assert_eq!(cpu.register_x, 0x01);
    //     assert_status(&cpu, FLAG_BREAK);
    //     assert_eq!(cpu.program_counter, 0x4032);
    //     assert_eq!(cpu.stack_pointer, 0xFD);
    //     assert_eq!(cpu.mem_read_u16(0x01FE), 0x8003);
    // }

    // // RTS
    // #[test]
    // fn test_rts() {
    //     let cpu = run(vec![0x60, 0x00], |cpu| {
    //         cpu.mem_write(0x01FF, 0x05);
    //         cpu.mem_write(0x01FE, 0x06);

    //         cpu.mem_write(0x0506, 0xe8);
    //         cpu.mem_write(0x0507, 0x00);

    //         cpu.stack_pointer = 0xFD;
    //     });
    //     assert_eq!(cpu.register_x, 0x01);
    //     assert_status(&cpu, 0);
    //     assert_eq!(cpu.program_counter, 0x0508);
    //     assert_eq!(cpu.stack_pointer, 0xFF);
    //     // 書き潰されない前提
    //     assert_eq!(cpu.mem_read_u16(0x01FE), 0x0506);
    // }

    // // JSR & RTS
    // #[test]
    // fn test_jsr_and_rts() {
    //     let cpu = run(vec![0x20, 0x30, 0x40, 0x00], |cpu| {
    //         cpu.mem_write(0x4030, 0xe8);
    //         cpu.mem_write(0x4031, 0x60); // RTS
    //         cpu.mem_write(0x4032, 0x00);
    //     });
    //     assert_eq!(cpu.register_x, 0x01);
    //     assert_status(&cpu, 0);
    //     assert_eq!(cpu.program_counter, 0x8004);
    //     assert_eq!(cpu.stack_pointer, 0xFF);
    //     // 書き潰されない前提
    //     assert_eq!(cpu.mem_read_u16(0x01FE), 0x8003);
    // }

    // LDX
    #[test]
    fn test_ldx() {
        let cpu = run(vec![0xa2, 0x05, 0x00], |_| {});
        assert_eq!(cpu.register_x, 0x05);
        assert_status(&cpu, FLAG_BREAK);
    }

    // LDY
    #[test]
    fn test_ldy() {
        let cpu = run(vec![0xa0, 0x05, 0x00], |_| {});
        assert_eq!(cpu.register_y, 0x05);
        assert_status(&cpu, FLAG_BREAK);
    }

    // NOP
    #[test]
    fn test_nop() {
        let cpu = run(vec![0xea, 0x00], |_| {});
        assert_eq!(cpu.program_counter, 0x8002);
        assert_status(&cpu, FLAG_BREAK);
    }

    // // PHA
    // #[test]
    // fn test_pha() {
    //     let cpu = run(vec![0x48, 0x00], |cpu| {
    //         cpu.register_a = 0x07;
    //     });
    //     assert_status(&cpu, 0);
    //     assert_eq!(cpu.register_a, 0x07);
    //     assert_eq!(cpu.stack_pointer, 0xFE);
    //     assert_eq!(cpu.mem_read(0x01FF), 0x07);
    // }

    // // PLA
    // #[test]
    // fn test_pla() {
    //     let cpu = run(vec![0x68, 0x00], |cpu| {
    //         cpu.mem_write(0x01FF, 0x07);
    //         cpu.stack_pointer = 0xFE;
    //     });
    //     assert_eq!(cpu.register_a, 0x07);
    //     assert_status(&cpu, 0);
    //     assert_eq!(cpu.stack_pointer, 0xFF);
    // }

    // #[test]
    // fn test_pla_zero() {
    //     let cpu = run(vec![0x68, 0x00], |cpu| {
    //         cpu.mem_write(0x01FF, 0x00);
    //         cpu.stack_pointer = 0xFE;
    //     });
    //     assert_eq!(cpu.register_a, 0x00);
    //     assert_status(&cpu, FLAG_ZERO);
    //     assert_eq!(cpu.stack_pointer, 0xFF);
    // }

    // // PHA & PLA
    // #[test]
    // fn test_pla_and_pla() {
    //     let cpu = run(vec![0x48, 0xa9, 0x60, 0x68, 0x00], |cpu| {
    //         cpu.register_a = 0x80;
    //     });
    //     assert_eq!(cpu.register_a, 0x80);
    //     assert_status(&cpu, FLAG_NEGATIVE);
    //     assert_eq!(cpu.stack_pointer, 0xFF);
    //     assert_eq!(cpu.program_counter, 0x8005);
    // }

    // // PHP
    // #[test]
    // fn test_php() {
    //     let cpu = run(vec![0x08, 0x00], |cpu| {
    //         cpu.status = FLAG_NEGATIVE | FLAG_OVERFLOW;
    //     });
    //     assert_status(&cpu, FLAG_NEGATIVE | FLAG_OVERFLOW);
    //     assert_eq!(cpu.stack_pointer, 0xFE);
    //     assert_eq!(cpu.mem_read(0x01FF), FLAG_NEGATIVE | FLAG_OVERFLOW);
    // }

    // // PLP
    // #[test]
    // fn test_plp() {
    //     let cpu = run(vec![0x28, 0x00], |cpu| {
    //         cpu.mem_write(0x01FF, FLAG_CARRY | FLAG_ZERO);
    //         cpu.stack_pointer = 0xFE;
    //     });
    //     assert_status(&cpu, FLAG_CARRY | FLAG_ZERO);
    //     assert_eq!(cpu.stack_pointer, 0xFF);
    // }

    // // PHP & PLP
    // #[test]
    // fn test_plp_and_plp() {
    //     let cpu = run(vec![0x08, 0xa9, 0xF0, 0x28, 0x00], |cpu| {
    //         cpu.status = FLAG_OVERFLOW | FLAG_CARRY;
    //     });
    //     assert_eq!(cpu.register_a, 0xF0);
    //     assert_status(&cpu, FLAG_OVERFLOW | FLAG_CARRY);
    //     assert_eq!(cpu.stack_pointer, 0xFF);
    //     assert_eq!(cpu.program_counter, 0x8005);
    // }

    // // FIXME RTIのテストは一旦保留
    // // BRKの逆をやるのだが、BRKでpushしてないぽいので。

    // STX
    #[test]
    fn test_stx() {
        let cpu = run(vec![0x86, 0x10, 0x00], |cpu| {
            cpu.register_x = 0xBA;
        });
        assert_eq!(cpu.mem_read(0x10), 0xBA);
    }

    // STY
    #[test]
    fn test_sty() {
        let cpu = run(vec![0x84, 0x10, 0x00], |cpu| {
            cpu.register_y = 0xBA;
        });
        assert_eq!(cpu.mem_read(0x10), 0xBA);
    }

    // TAX
    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let cpu = run(vec![0xaa, 0x00], |cpu| {
            cpu.register_a = 10;
        });
        assert_eq!(cpu.register_x, 10);
    }

    // TXA
    #[test]
    fn test_txa() {
        let cpu = run(vec![0x8a, 0x00], |cpu| {
            cpu.register_x = 0x10;
        });
        assert_eq!(cpu.register_a, 0x10);
    }

    // TAY
    #[test]
    fn test_tay() {
        let cpu = run(vec![0xa8, 0x00], |cpu| {
            cpu.register_a = 0x10;
        });
        assert_eq!(cpu.register_y, 0x10);
    }

    // TYA
    #[test]
    fn test_tya() {
        let cpu = run(vec![0x98, 0x00], |cpu| {
            cpu.register_y = 0x10;
        });
        assert_eq!(cpu.register_a, 0x10);
    }

    // // TSX
    // #[test]
    // fn test_tsx() {
    //     let cpu = run(vec![0xba, 0x00], |_| {});
    //     assert_eq!(cpu.register_x, 0xFF);
    //     assert_status(&cpu, FLAG_NEGATIVE);
    // }

    // #[test]
    // fn test_tsx_some_value() {
    //     let cpu = run(vec![0xba, 0x00], |cpu| {
    //         cpu.stack_pointer = 0x75;
    //     });
    //     assert_eq!(cpu.register_x, 0x75);
    //     assert_status(&cpu, 0);
    // }

    // // TXS
    // #[test]
    // fn test_txs() {
    //     let cpu = run(vec![0x9a, 0x00], |cpu| {
    //         cpu.register_x = 0x80;
    //     });
    //     assert_eq!(cpu.stack_pointer, 0x80);
    //     assert_status(&cpu, 0);
    // }
}
