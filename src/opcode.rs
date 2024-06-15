#[rustfmt::skip]
#[derive(PartialEq, Debug)]
pub enum Instruction {
    ADC, AND, ASL, BCC, BCS, BEQ, BIT, BMI, BNE, BPL,
    BRK, BVC, BVS, CLC, CLD, CLI, CLV, CMP, CPX, CPY,
    DEC, DEX, DEY, EOR, INC, INX, INY, JMP, JSR, LDA,
    LDX, LDY, LSR, NOP, ORA, PHA, PHP, PLA, PLP, ROL,
    ROR, RTI, RTS, SBC, SEC, SED, SEI, STA, STX, STY,
    TAX, TAY, TSX, TXA, TXS, TYA,
}

#[derive(PartialEq, Debug)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    Indirect,
    IndirectX,
    IndirectY,
    Accumulator,
    Relative,
    Implied,
}

#[derive(Debug)]
pub struct Opcode {
    pub binary: u8,
    pub instruction: Instruction,
    pub addressing_mode: AddressingMode,
    pub bytes: u8,
    pub cycles: u8,
}

pub fn decode(binary: u8) -> &'static Opcode {
    &OPCODES[binary as usize]
}

#[rustfmt::skip]
const OPCODES: [Opcode; 0x100] = [
    Opcode{binary: 0x00, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x01, instruction: Instruction::ORA, bytes: 2, cycles: 6, addressing_mode: AddressingMode::IndirectX},
    Opcode{binary: 0x02, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x03, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x04, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x05, instruction: Instruction::ORA, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x06, instruction: Instruction::ASL, bytes: 2, cycles: 5, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x07, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x08, instruction: Instruction::PHP, bytes: 1, cycles: 3, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x09, instruction: Instruction::ORA, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0x0A, instruction: Instruction::ASL, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Accumulator},
    Opcode{binary: 0x0B, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x0C, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x0D, instruction: Instruction::ORA, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x0E, instruction: Instruction::ASL, bytes: 3, cycles: 6, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x0F, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x10, instruction: Instruction::BPL, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Relative},
    Opcode{binary: 0x11, instruction: Instruction::ORA, bytes: 2, cycles: 5, addressing_mode: AddressingMode::IndirectY},
    Opcode{binary: 0x12, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x13, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x14, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x15, instruction: Instruction::ORA, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0x16, instruction: Instruction::ASL, bytes: 2, cycles: 6, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0x17, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x18, instruction: Instruction::CLC, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x19, instruction: Instruction::ORA, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteY},
    Opcode{binary: 0x1A, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x1B, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x1C, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x1D, instruction: Instruction::ORA, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0x1E, instruction: Instruction::ASL, bytes: 3, cycles: 7, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0x1F, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x20, instruction: Instruction::JSR, bytes: 3, cycles: 6, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x21, instruction: Instruction::AND, bytes: 2, cycles: 6, addressing_mode: AddressingMode::IndirectX},
    Opcode{binary: 0x22, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x23, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x24, instruction: Instruction::BIT, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x25, instruction: Instruction::AND, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x26, instruction: Instruction::ROL, bytes: 2, cycles: 5, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x27, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x28, instruction: Instruction::PLP, bytes: 1, cycles: 4, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x29, instruction: Instruction::AND, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0x2A, instruction: Instruction::ROL, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Accumulator},
    Opcode{binary: 0x2B, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x2C, instruction: Instruction::BIT, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x2D, instruction: Instruction::AND, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x2E, instruction: Instruction::ROL, bytes: 3, cycles: 6, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x2F, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x30, instruction: Instruction::BMI, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Relative},
    Opcode{binary: 0x31, instruction: Instruction::AND, bytes: 2, cycles: 5, addressing_mode: AddressingMode::IndirectY},
    Opcode{binary: 0x32, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x33, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x34, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x35, instruction: Instruction::AND, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0x36, instruction: Instruction::ROL, bytes: 2, cycles: 6, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0x37, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x38, instruction: Instruction::SEC, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x39, instruction: Instruction::AND, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteY},
    Opcode{binary: 0x3A, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x3B, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x3C, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x3D, instruction: Instruction::AND, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0x3E, instruction: Instruction::ROL, bytes: 3, cycles: 7, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0x3F, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x40, instruction: Instruction::RTI, bytes: 1, cycles: 6, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x41, instruction: Instruction::EOR, bytes: 2, cycles: 6, addressing_mode: AddressingMode::IndirectX},
    Opcode{binary: 0x42, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x43, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x44, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x45, instruction: Instruction::EOR, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x46, instruction: Instruction::LSR, bytes: 2, cycles: 5, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x47, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x48, instruction: Instruction::PHA, bytes: 1, cycles: 3, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x49, instruction: Instruction::EOR, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0x4A, instruction: Instruction::LSR, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Accumulator},
    Opcode{binary: 0x4B, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x4C, instruction: Instruction::JMP, bytes: 3, cycles: 3, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x4D, instruction: Instruction::EOR, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x4E, instruction: Instruction::LSR, bytes: 3, cycles: 6, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x4F, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x50, instruction: Instruction::BVC, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Relative},
    Opcode{binary: 0x51, instruction: Instruction::EOR, bytes: 2, cycles: 5, addressing_mode: AddressingMode::IndirectY},
    Opcode{binary: 0x52, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x53, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x54, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x55, instruction: Instruction::EOR, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0x56, instruction: Instruction::LSR, bytes: 2, cycles: 6, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0x57, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x58, instruction: Instruction::CLI, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x59, instruction: Instruction::EOR, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteY},
    Opcode{binary: 0x5A, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x5B, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x5C, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x5D, instruction: Instruction::EOR, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0x5E, instruction: Instruction::LSR, bytes: 3, cycles: 7, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0x5F, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x60, instruction: Instruction::RTS, bytes: 1, cycles: 6, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x61, instruction: Instruction::ADC, bytes: 2, cycles: 6, addressing_mode: AddressingMode::IndirectX},
    Opcode{binary: 0x62, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x63, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x64, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x65, instruction: Instruction::ADC, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x66, instruction: Instruction::ROR, bytes: 2, cycles: 5, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x67, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x68, instruction: Instruction::PLA, bytes: 1, cycles: 4, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x69, instruction: Instruction::ADC, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0x6A, instruction: Instruction::ROR, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Accumulator},
    Opcode{binary: 0x6B, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x6C, instruction: Instruction::JMP, bytes: 3, cycles: 5, addressing_mode: AddressingMode::Indirect},
    Opcode{binary: 0x6D, instruction: Instruction::ADC, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x6E, instruction: Instruction::ROR, bytes: 3, cycles: 6, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x6F, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x70, instruction: Instruction::BVS, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Relative},
    Opcode{binary: 0x71, instruction: Instruction::ADC, bytes: 2, cycles: 5, addressing_mode: AddressingMode::IndirectY},
    Opcode{binary: 0x72, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x73, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x74, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x75, instruction: Instruction::ADC, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0x76, instruction: Instruction::ROR, bytes: 2, cycles: 6, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0x77, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x78, instruction: Instruction::SEI, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x79, instruction: Instruction::ADC, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteY},
    Opcode{binary: 0x7A, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x7B, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x7C, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x7D, instruction: Instruction::ADC, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0x7E, instruction: Instruction::ROR, bytes: 3, cycles: 7, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0x7F, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x80, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x81, instruction: Instruction::STA, bytes: 2, cycles: 6, addressing_mode: AddressingMode::IndirectX},
    Opcode{binary: 0x82, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x83, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x84, instruction: Instruction::STY, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x85, instruction: Instruction::STA, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x86, instruction: Instruction::STX, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0x87, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x88, instruction: Instruction::DEY, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x89, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x8A, instruction: Instruction::TXA, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x8B, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x8C, instruction: Instruction::STY, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x8D, instruction: Instruction::STA, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x8E, instruction: Instruction::STX, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0x8F, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x90, instruction: Instruction::BCC, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Relative},
    Opcode{binary: 0x91, instruction: Instruction::STA, bytes: 2, cycles: 6, addressing_mode: AddressingMode::IndirectY},
    Opcode{binary: 0x92, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x93, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x94, instruction: Instruction::STY, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0x95, instruction: Instruction::STA, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0x96, instruction: Instruction::STX, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageY},
    Opcode{binary: 0x97, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x98, instruction: Instruction::TYA, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x99, instruction: Instruction::STA, bytes: 3, cycles: 5, addressing_mode: AddressingMode::AbsoluteY},
    Opcode{binary: 0x9A, instruction: Instruction::TXS, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x9B, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x9C, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x9D, instruction: Instruction::STA, bytes: 3, cycles: 5, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0x9E, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0x9F, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xA0, instruction: Instruction::LDY, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0xA1, instruction: Instruction::LDA, bytes: 2, cycles: 6, addressing_mode: AddressingMode::IndirectX},
    Opcode{binary: 0xA2, instruction: Instruction::LDX, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0xA3, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xA4, instruction: Instruction::LDY, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0xA5, instruction: Instruction::LDA, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0xA6, instruction: Instruction::LDX, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0xA7, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xA8, instruction: Instruction::TAY, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xA9, instruction: Instruction::LDA, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0xAA, instruction: Instruction::TAX, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xAB, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xAC, instruction: Instruction::LDY, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0xAD, instruction: Instruction::LDA, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0xAE, instruction: Instruction::LDX, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0xAF, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xB0, instruction: Instruction::BCS, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Relative},
    Opcode{binary: 0xB1, instruction: Instruction::LDA, bytes: 2, cycles: 5, addressing_mode: AddressingMode::IndirectY},
    Opcode{binary: 0xB2, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xB3, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xB4, instruction: Instruction::LDY, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0xB5, instruction: Instruction::LDA, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0xB6, instruction: Instruction::LDX, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageY},
    Opcode{binary: 0xB7, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xB8, instruction: Instruction::CLV, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xB9, instruction: Instruction::LDA, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteY},
    Opcode{binary: 0xBA, instruction: Instruction::TSX, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xBB, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xBC, instruction: Instruction::LDY, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0xBD, instruction: Instruction::LDA, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0xBE, instruction: Instruction::LDX, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteY},
    Opcode{binary: 0xBF, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xC0, instruction: Instruction::CPY, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0xC1, instruction: Instruction::CMP, bytes: 2, cycles: 6, addressing_mode: AddressingMode::IndirectX},
    Opcode{binary: 0xC2, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xC3, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xC4, instruction: Instruction::CPY, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0xC5, instruction: Instruction::CMP, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0xC6, instruction: Instruction::DEC, bytes: 2, cycles: 5, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0xC7, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xC8, instruction: Instruction::INY, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xC9, instruction: Instruction::CMP, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0xCA, instruction: Instruction::DEX, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xCB, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xCC, instruction: Instruction::CPY, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0xCD, instruction: Instruction::CMP, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0xCE, instruction: Instruction::DEC, bytes: 3, cycles: 6, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0xCF, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xD0, instruction: Instruction::BNE, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Relative},
    Opcode{binary: 0xD1, instruction: Instruction::CMP, bytes: 2, cycles: 5, addressing_mode: AddressingMode::IndirectY},
    Opcode{binary: 0xD2, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xD3, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xD4, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xD5, instruction: Instruction::CMP, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0xD6, instruction: Instruction::DEC, bytes: 2, cycles: 6, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0xD7, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xD8, instruction: Instruction::CLD, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xD9, instruction: Instruction::CMP, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteY},
    Opcode{binary: 0xDA, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xDB, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xDC, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xDD, instruction: Instruction::CMP, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0xDE, instruction: Instruction::DEC, bytes: 3, cycles: 7, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0xDF, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xE0, instruction: Instruction::CPX, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0xE1, instruction: Instruction::SBC, bytes: 2, cycles: 6, addressing_mode: AddressingMode::IndirectX},
    Opcode{binary: 0xE2, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xE3, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xE4, instruction: Instruction::CPX, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0xE5, instruction: Instruction::SBC, bytes: 2, cycles: 3, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0xE6, instruction: Instruction::INC, bytes: 2, cycles: 5, addressing_mode: AddressingMode::ZeroPage},
    Opcode{binary: 0xE7, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xE8, instruction: Instruction::INX, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xE9, instruction: Instruction::SBC, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Immediate},
    Opcode{binary: 0xEA, instruction: Instruction::NOP, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xEB, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xEC, instruction: Instruction::CPX, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0xED, instruction: Instruction::SBC, bytes: 3, cycles: 4, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0xEE, instruction: Instruction::INC, bytes: 3, cycles: 6, addressing_mode: AddressingMode::Absolute},
    Opcode{binary: 0xEF, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xF0, instruction: Instruction::BEQ, bytes: 2, cycles: 2, addressing_mode: AddressingMode::Relative},
    Opcode{binary: 0xF1, instruction: Instruction::SBC, bytes: 2, cycles: 5, addressing_mode: AddressingMode::IndirectY},
    Opcode{binary: 0xF2, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xF3, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xF4, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xF5, instruction: Instruction::SBC, bytes: 2, cycles: 4, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0xF6, instruction: Instruction::INC, bytes: 2, cycles: 6, addressing_mode: AddressingMode::ZeroPageX},
    Opcode{binary: 0xF7, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xF8, instruction: Instruction::SED, bytes: 1, cycles: 2, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xF9, instruction: Instruction::SBC, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteY},
    Opcode{binary: 0xFA, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xFB, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xFC, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
    Opcode{binary: 0xFD, instruction: Instruction::SBC, bytes: 3, cycles: 4, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0xFE, instruction: Instruction::INC, bytes: 3, cycles: 7, addressing_mode: AddressingMode::AbsoluteX},
    Opcode{binary: 0xFF, instruction: Instruction::BRK, bytes: 1, cycles: 7, addressing_mode: AddressingMode::Implied},
];
