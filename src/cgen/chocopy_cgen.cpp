#include "chocopy_cgen.hpp"

#include <fmt/core.h>

#include <cassert>
#include <iostream>
#include <map>
#include <memory>
#include <ostream>
#include <ranges>
#include <regex>
#include <stack>
#include <string>
#include <type_traits>
#include <utility>

#include "BasicBlock.hpp"
#include "Class.hpp"
#include "Constant.hpp"
#include "Function.hpp"
#include "GlobalVariable.hpp"
#include "InstGen.hpp"
#include "Module.hpp"
#include "RiscVBackEnd.hpp"
#include "Type.hpp"
#include "Value.hpp"
#include "chocopy_lightir.hpp"

using namespace lightir;

static LightWalker *light_walker;

namespace cgen {
const auto fp = InstGen::Reg("fp");
const auto sp = InstGen::Reg("sp");
const auto ra = InstGen::Reg("ra");

const auto a0 = InstGen::Reg("a0");
const auto a1 = InstGen::Reg("a1");
const auto a2 = InstGen::Reg("a2");
const auto a3 = InstGen::Reg("a3");
const auto a4 = InstGen::Reg("a4");
const auto a5 = InstGen::Reg("a5");
const auto a6 = InstGen::Reg("a6");
const auto a7 = InstGen::Reg("a7");

const auto t0 = InstGen::Reg("t0");
const auto t1 = InstGen::Reg("t1");

const auto s1 = InstGen::Reg("s1");

const auto zero = InstGen::Reg("zero");
int offset = 0;

map<string, int> *mapping;
map<string, int> *alloca_vars;
map<string, string> global_map;
string CodeGen::generateModuleCode() {
    string asm_code;
    asm_code += ".data\n";
    for (auto &classInfo : this->module->get_class()) {
        asm_code += backend->emit_prototype(*classInfo);
        global_map.insert({classInfo->get_name(), classInfo->prototype_label_});
    }
    asm_code += generateGlobalVarsCode();

    asm_code += ".text\n";
    for (auto func : this->module->get_functions()) {
        assert(dynamic_cast<Function *>(func));
        if (func->get_basic_blocks().size()) {
            asm_code += CodeGen::generateFunctionCode(func);
        }
    }
    return asm_code;
}

string CodeGen::generateFunctionCode(Function *func) {
    string asm_code;
    asm_code +=
        fmt::format(".globl {}\n{}:\n", func->get_name(), func->get_name());
    current_function = func;
    // TODO: Generate function code

    /*
        fp  ->
            ->  (saved) ra
            ->  (saved) fp
    */

    map<string, int> local_vars;
    map<string, int> local_alloca;
    mapping = &local_vars;
    alloca_vars = &local_alloca;

    asm_code += "\n  # setup begin\n";

    // save ra (for itself) & fp (for caller)
    asm_code += backend->emit_addi(sp, sp, -8);
    asm_code += backend->emit_sw(ra, sp, 4);  // saved ra at -4(fp)
    asm_code += backend->emit_sw(fp, sp, 0);  // saved fp at -8(fp)

    // set up fp
    asm_code += backend->emit_addi(fp, sp, 8);
    offset = -8;

    // create mapping for arg
    for (auto &arg : func->get_args()) {
        string op_name = arg->get_name();

        auto arg_num = atoi(op_name.c_str() + 3);
        // from register
        if (arg_num < 8) {
            offset -= 4;
            asm_code += backend->emit_sw(InstGen::Reg("a" + to_string(arg_num)),
                                         fp, offset);
            asm_code += backend->emit_addi(sp, fp, offset);
            mapping->insert({arg->get_name(), offset});

            // asm_code += backend->emit_addi(sp, sp, -4);
            // asm_code +=
            //     backend->emit_sw(InstGen::Reg("a" + to_string(arg_num)), sp,
            //     0);
            // offset -= 4;
            // mapping->insert({arg->get_name(), offset});
        }
        // from stack
        else {
            auto stack_num = arg_num - 8;
            // asm_code += stackToReg(InstGen::Addr(fp, stack_num * 4), a0);

            // offset -= 4;
            // asm_code += backend->emit_sw(a0, fp, offset);
            // asm_code += backend->emit_addi(sp, fp, offset);
            mapping->insert({arg->get_name(), stack_num * 4});
        }
    }
    asm_code += "  # setup end\n\n";

    for (auto &bb : func->get_basic_blocks()) {
        asm_code += func->get_name() + "$" + bb->get_name() + ":\n";
        asm_code += generateBasicBlockCode(bb);
    }
    return asm_code;
}

CodeGen::CodeGen(shared_ptr<Module> module) : module(std::move(module)) {}

string CodeGen::generateBasicBlockCode(BasicBlock *bb) {
    std::string asm_code;
    current_basic_block = bb;
    for (auto &inst : bb->get_instructions()) {
        asm_code += CodeGen::generateInstructionCode(inst);
    }
    asm_code += generateBasicBlockPostCode(bb);
    return asm_code;
}
string CodeGen::generateBasicBlockPostCode(BasicBlock *bb) {
    std::string asm_code;
    // TODO: Generate phi code
    return asm_code;
}

string CodeGen::getOperand(Value *op, bool get_lvalue) {
    std::string asm_code;
    // cerr << op->get_name() << endl;
    if (auto const_op = dynamic_cast<lightir::ConstantNull *>(op); const_op) {
        asm_code += backend->emit_li(a0, 0);
    } else if (auto const_op = dynamic_cast<lightir::ConstantInt *>(op);
               const_op) {
        asm_code += backend->emit_li(a0, const_op->get_value());
    } else {
        string op_name = op->get_name();
        // local virtual reg
        if (mapping->contains(op_name)) {
            int fp_offset = (*mapping)[op_name];
            // cout << op_name << " " << fp_offset << endl;
            if (get_lvalue) {  // lvalue
                if (-2048 <= fp_offset && fp_offset < 2048)
                    asm_code += backend->emit_addi(a0, fp, fp_offset);
                else {
                    asm_code += backend->emit_li(a0, fp_offset);
                    asm_code += backend->emit_add(a0, fp, a0);
                }
            } else  // rvalue
                asm_code += stackToReg(InstGen::Addr(fp, fp_offset), a0);
        } else if (alloca_vars->contains(op_name)) {
            int fp_offset = (*alloca_vars)[op_name];
            // cerr << op_name << " " << backend->emit_addi(a0, fp, fp_offset)
            //      << endl;
            if (-2048 <= fp_offset && fp_offset < 2048)
                asm_code += backend->emit_addi(a0, fp, fp_offset);
            else {
                asm_code += backend->emit_li(a0, fp_offset);
                asm_code += backend->emit_add(a0, fp, a0);
            }
        }
        // global
        else {
            // cout << ">>  " << op_name << endl;
            string label_str = global_map[op_name];
            // cout << label_str << endl;
            // cout << backend->emit_lw(a0, InstGen::Addr(label_str)) << endl;
            asm_code += backend->emit_la(a0, InstGen::Addr(label_str));
        }
    }
    return asm_code;
}

string CodeGen::generateInstructionCode(Instruction *inst) {
    using Reg = InstGen::Reg;
    using Addr = InstGen::Addr;
    std::string asm_code;
    auto &ops = inst->get_operands();
    // TODO: Generate instruction code
    switch (inst->get_instr_type()) {
        case lightir::Instruction::Ret: {
            auto ret_inst = dynamic_cast<lightir::ReturnInst *>(inst);
            if (!ret_inst->is_void_ret()) {
                asm_code += getOperand(ret_inst->get_operand(0), false);
            }
            asm_code += "\n  # cleanup begin\n";
            asm_code += backend->emit_mv(sp, fp);
            asm_code += backend->emit_lw(ra, fp, -4);
            asm_code += backend->emit_lw(fp, fp, -8);
            asm_code += "  # cleanup end\n\n";

            asm_code += "\n  # Ret begin\n";
            asm_code += backend->emit_jr(ra);
            asm_code += "  # Ret end\n\n";
            break;
        }
        case lightir::Instruction::Br: {
            asm_code += "\n  # Branch Begin\n";
            auto br_inst = dynamic_cast<lightir::BranchInst *>(inst);
            // cond br
            if (br_inst->is_cond_br()) {
                auto val = br_inst->get_operand(0);
                auto branch_true = br_inst->get_operand(1)->get_name();
                auto branch_false = br_inst->get_operand(2)->get_name();
                asm_code += getOperand(val, false);
                asm_code += backend->emit_bne(
                    a0, zero,
                    InstGen::Addr(current_function->get_name() + "$" +
                                  branch_true));
                asm_code += backend->emit_j(current_function->get_name() + "$" +
                                            branch_false);
            }
            // unconditional
            else {
                asm_code +=
                    backend->emit_j(current_function->get_name() + "$" +
                                    br_inst->get_operand(0)->get_name());
            }
            asm_code += "  # Branch End\n\n";
            break;
        }
        case lightir::Instruction::Neg:
        case lightir::Instruction::Not: {
            break;
        }
        case lightir::Instruction::Add:
        case lightir::Instruction::Sub:
        case lightir::Instruction::Mul:
        case lightir::Instruction::Div:
        case lightir::Instruction::Rem:
        case lightir::Instruction::And:
        case lightir::Instruction::Or: {
            asm_code += "\n  # Binary Op begin\n";
            auto add_inst = dynamic_cast<lightir::BinaryInst *>(inst);
            auto v1 = add_inst->get_operand(0);
            auto v2 = add_inst->get_operand(1);
            asm_code += getOperand(v1, false);

            asm_code += backend->emit_addi(sp, sp, -4);
            asm_code += backend->emit_sw(a0, sp, 0);
            asm_code += getOperand(v2, false);
            asm_code += backend->emit_lw(t0, sp, 0);
            asm_code += backend->emit_addi(sp, sp, 4);

            switch (inst->get_instr_type()) {
                case lightir::Instruction::Add:
                    asm_code += backend->emit_add(a0, t0, a0);
                    break;
                case lightir::Instruction::Sub: {
                    // cerr << inst->print() << endl;
                    if (auto const_op =
                            dynamic_cast<lightir::ConstantInt *>(v1);
                        const_op && v2->get_type() == module->get_int1_type()) {
                        if (const_op->get_value() == 1) {
                            asm_code += backend->emit_xori(a0, a0, 1);
                        }
                    } else {
                        asm_code += backend->emit_sub(a0, t0, a0);
                    }
                    break;
                }
                case lightir::Instruction::Mul:
                    asm_code += backend->emit_mul(a0, t0, a0);
                    break;
                case lightir::Instruction::Div:
                    asm_code += backend->emit_div(a0, t0, a0);
                    break;
                case lightir::Instruction::Rem:
                    asm_code += backend->emit_rem(a0, t0, a0);
                    break;
                case lightir::Instruction::And:
                    asm_code += backend->emit_and(a0, t0, a0);
                    break;
                case lightir::Instruction::Or:
                    asm_code += backend->emit_or(a0, t0, a0);
                    break;
                default:
                    cerr << "Error in Binary Inst" << endl;
            }

            // save virtual reg
            offset -= 4;
            asm_code += backend->emit_sw(a0, fp, offset);
            asm_code += backend->emit_addi(sp, fp, offset);
            mapping->insert({add_inst->get_name(), offset});

            // asm_code += backend->emit_addi(sp, sp, -4);
            // asm_code += backend->emit_sw(a0, sp, 0);
            // offset -= 4;
            // mapping->insert({add_inst->get_name(), offset});
            // cerr << add_inst->get_name() << " " << offset << endl;

            asm_code += "  # Binary Op end\n\n";
            break;
        }
        case lightir::Instruction::Alloca: {
            auto alloca_inst = dynamic_cast<lightir::AllocaInst *>(inst);
            auto alloca_type = alloca_inst->get_alloca_type();
            asm_code += "\n  # Alloca Begin\n";
            int size = 0;
            // Class
            if (auto class_ = dynamic_cast<lightir::Class *>(alloca_type);
                class_) {
                size = class_->get_attribute()->size() * 4;
            } else {
                size = 4;
            }
            // allocate
            asm_code += backend->emit_addi(sp, sp, -size);
            offset -= size;

            alloca_vars->insert({alloca_inst->get_name(), offset});

            asm_code += "  # Alloca End\n\n";
            break;
        }
        case lightir::Instruction::Load: {
            auto load_inst = dynamic_cast<lightir::LoadInst *>(inst);
            auto ptr = load_inst->get_lval();  // a0

            // cerr << inst->print() << endl;
            asm_code += getOperand(ptr, false);
            asm_code += backend->emit_lw(a0, InstGen::Addr(a0, 0));

            // asm_code += backend->emit_addi(sp, sp, -4);
            // asm_code += backend->emit_sw(a0, sp, 0);
            // offset -= 4;
            // mapping->insert({load_inst->get_name(), offset});
            offset -= 4;
            asm_code += backend->emit_sw(a0, fp, offset);
            asm_code += backend->emit_addi(sp, fp, offset);
            mapping->insert({load_inst->get_name(), offset});

            break;
        }
        case lightir::Instruction::Store: {
            auto store_inst = dynamic_cast<lightir::StoreInst *>(inst);
            auto ptr = store_inst->get_lval();  // t0
            auto val = store_inst->get_rval();  // a0

            asm_code += getOperand(ptr, false);
            asm_code += backend->emit_addi(sp, sp, -4);
            asm_code += backend->emit_sw(a0, sp, 0);

            asm_code += getOperand(val, false);
            asm_code += backend->emit_lw(t0, sp, 0);
            asm_code += backend->emit_addi(sp, sp, 4);

            asm_code += regToStack(a0, InstGen::Addr(t0, 0));

            break;
        }
        case lightir::Instruction::ICmp: {
            auto icmp_inst = dynamic_cast<lightir::CmpInst *>(inst);

            auto lhs = icmp_inst->get_operand(0);  // t0
            auto rhs = icmp_inst->get_operand(1);  // a0

            asm_code += getOperand(lhs, false);
            asm_code += backend->emit_addi(sp, sp, -4);
            asm_code += backend->emit_sw(a0, sp, 0);

            asm_code += getOperand(rhs, false);
            asm_code += backend->emit_lw(t0, sp, 0);
            asm_code += backend->emit_addi(sp, sp, 4);

            // ==
            if (icmp_inst->get_cmp_op() == lightir::CmpInst::EQ) {
                asm_code += backend->emit_sub(a0, t0, a0);
                asm_code += backend->emit_seqz(a0, a0);
            }
            // !=
            else if (icmp_inst->get_cmp_op() == lightir::CmpInst::NE) {
                asm_code += backend->emit_sub(a0, a0, t0);
                asm_code += backend->emit_snez(a0, a0);
            }
            // >=
            else if (icmp_inst->get_cmp_op() == lightir::CmpInst::GE) {
                asm_code += backend->emit_sub(a0, t0, a0);
                asm_code += backend->emit_slt(a0, a0, zero);
                asm_code += backend->emit_xori(a0, a0, 1);
            }
            // >
            else if (icmp_inst->get_cmp_op() == lightir::CmpInst::GT) {
                asm_code += backend->emit_sub(a0, t0, a0);
                asm_code += backend->emit_snez(t0, a0);  // t0 !=
                asm_code += backend->emit_slt(a0, a0, zero);
                asm_code += backend->emit_xori(a0, a0, 1);  //  a0 >=
                asm_code += backend->emit_and(a0, a0, t0);
            }
            // <=
            else if (icmp_inst->get_cmp_op() == lightir::CmpInst::LE) {
                asm_code += backend->emit_sub(a0, t0, a0);
                asm_code += backend->emit_seqz(t0, a0);       // t0 ==
                asm_code += backend->emit_slt(a0, a0, zero);  //  a0 <
                asm_code += backend->emit_or(a0, a0, t0);
            }
            // <
            else if (icmp_inst->get_cmp_op() == lightir::CmpInst::LT) {
                asm_code += backend->emit_slt(a0, t0, a0);
            }

            // asm_code += backend->emit_addi(sp, sp, -4);
            // asm_code += backend->emit_sw(a0, sp, 0);
            // offset -= 4;
            // mapping->insert({icmp_inst->get_name(), offset});

            offset -= 4;
            asm_code += backend->emit_sw(a0, fp, offset);
            asm_code += backend->emit_addi(sp, fp, offset);
            mapping->insert({icmp_inst->get_name(), offset});

            break;
        }
        case lightir::Instruction::PHI: {
            break;
        }
        case lightir::Instruction::Call: {
            asm_code += "\n  # Call begin\n";
            asm_code += generateFunctionCall(inst, inst->get_name(),
                                             inst->get_operands());
            asm_code += "  # Call end\n\n";
            break;
        }
        case lightir::Instruction::GEP: {
            auto gep_inst = dynamic_cast<lightir::GetElementPtrInst *>(inst);
            // cerr << "---GEP---" << endl;
            auto ptr = gep_inst->get_operand(0);  // t0
            auto idx = gep_inst->get_operand(1);  // a0

            asm_code += getOperand(ptr, false);
            asm_code += backend->emit_addi(sp, sp, -4);
            asm_code += backend->emit_sw(a0, sp, 0);

            asm_code += getOperand(idx, false);
            asm_code += backend->emit_lw(t0, sp, 0);
            asm_code += backend->emit_addi(sp, sp, 4);

            if (ptr->get_type() == module->get_ptr_i8_type()) {
            } else {
                asm_code += backend->emit_slli(a0, a0, 2);
            }
            // asm_code += backend->emit_add(a0, zero, zero);
            asm_code += backend->emit_add(a0, t0, a0);

            // asm_code += backend->emit_addi(sp, sp, -4);
            // asm_code += backend->emit_sw(a0, sp, 0);
            // offset -= 4;
            // mapping->insert({gep_inst->get_name(), offset});
            offset -= 4;
            asm_code += backend->emit_sw(a0, fp, offset);
            asm_code += backend->emit_addi(sp, fp, offset);
            mapping->insert({gep_inst->get_name(), offset});

            break;
        }
        case lightir::Instruction::ZExt: {
            auto zext_inst = dynamic_cast<lightir::ZextInst *>(inst);
            auto val = zext_inst->get_operand(0);
            asm_code += getOperand(val, true);

            // asm_code += backend->emit_addi(sp, sp, -4);
            // asm_code += backend->emit_sw(a0, sp, 0);
            // offset -= 4;
            // mapping->insert({zext_inst->get_name(), offset});
            offset -= 4;
            asm_code += backend->emit_sw(a0, fp, offset);
            asm_code += backend->emit_addi(sp, fp, offset);
            mapping->insert({zext_inst->get_name(), offset});

            break;
        }
        case lightir::Instruction::BitCast: {
            break;
        }
        case lightir::Instruction::ASM: {
            auto asm_inst = dynamic_cast<lightir::AsmInst *>(inst);
            auto newline = std::regex("\\\\0A");
            asm_code += "  " +
                        regex_replace(asm_inst->get_asm(), newline, "\n  ") +
                        "\n";
            break;
        }
        case lightir::Instruction::PtrToInt: {
            auto ptr_to_int_inst = dynamic_cast<lightir::PtrToIntInst *>(inst);
            auto val = ptr_to_int_inst->get_operand(0);
            asm_code += getOperand(val, false);
            offset -= 4;
            asm_code += backend->emit_sw(a0, fp, offset);
            asm_code += backend->emit_addi(sp, fp, offset);
            mapping->insert({ptr_to_int_inst->get_name(), offset});
            break;
        }
        case lightir::Instruction::InElem:
        case lightir::Instruction::ExElem:
        case lightir::Instruction::Trunc: {
            auto trunc_inst = dynamic_cast<lightir::TruncInst *>(inst);
            auto val = trunc_inst->get_operand(0);
            asm_code += getOperand(val, false);
            offset -= 4;
            asm_code += backend->emit_sw(a0, fp, offset);
            asm_code += backend->emit_addi(sp, fp, offset);
            mapping->insert({trunc_inst->get_name(), offset});
            break;
        }
        case lightir::Instruction::VExt:
        case lightir::Instruction::Shl:
        case lightir::Instruction::AShr:
        case lightir::Instruction::LShr:
            break;
    }
    return asm_code;
}
string CodeGen::generateFunctionCall(Instruction *inst, const string &call_inst,
                                     vector<Value *> ops) {
    string asm_code;
    // cout << "func  " << inst->get_operand(0)->get_name() << endl;
    // TODO: Generate function call code

    int stack_used = 0;
    // arg list non-empty
    if (inst->get_num_operand() > 1) {
        auto v1 = inst->get_operand(1);
        // cerr << "##  " << v1->print().substr(1) << endl;
        // v1->set_name(v1->print().substr(1));
        asm_code += getOperand(v1, false);

        // save a0
        asm_code += backend->emit_addi(sp, sp, -4);
        asm_code += backend->emit_sw(a0, sp, 0);
        // asm_code += backend->emit_mv(s1, a0);

        for (int i = 2; i <= 8 && i < inst->get_num_operand(); ++i) {
            auto val = inst->get_operand(i);
            // cerr << "##  " << val->get_name() << endl;

            // evaluate
            asm_code += getOperand(val, false);

            // in register
            if (i - 1 < 8) {
                asm_code +=
                    backend->emit_mv(InstGen::Reg("a" + to_string(i - 1)), a0);
            }
            // ! in stack
        }
        for (int i = inst->get_num_operand() - 1; i > 8; --i) {
            auto val = inst->get_operand(i);
            // evaluate
            asm_code += getOperand(val, false);

            asm_code += backend->emit_addi(sp, sp, -4);
            asm_code += backend->emit_sw(a0, sp, 0);

            ++stack_used;
        }
        // load a0
        asm_code += backend->emit_lw(a0, sp, 4 * stack_used);
        // ! stack recovered after calling function
        // ! asm_code += backend->emit_addi(sp, sp, 4);
        // asm_code += backend->emit_mv(a0, s1);
    }
    auto func = inst->get_operand(0);
    // not from dispatch table
    if (dynamic_cast<lightir::Function *>(func))
        asm_code += backend->emit_jal(InstGen::Addr(func->get_name()));
    // dispatch
    else {
        // save a0
        asm_code += backend->emit_addi(sp, sp, -4);
        asm_code += backend->emit_sw(a0, sp, 0);

        asm_code += getOperand(func, false);
        asm_code += backend->emit_mv(t0, a0);

        // load a0
        asm_code += backend->emit_lw(a0, sp, 0);
        asm_code += backend->emit_addi(sp, sp, 4);

        asm_code += backend->emit_jalr(t0);
    }

    // ! recovered stack used
    if (stack_used) {
        asm_code += backend->emit_addi(sp, sp, 4 * stack_used);
    }
    // ! used to store a0
    asm_code += backend->emit_addi(sp, sp, 4);

    // save return value
    if (!inst->is_void_ret()) {
        offset -= 4;
        asm_code += backend->emit_sw(a0, fp, offset);
        asm_code += backend->emit_addi(sp, fp, offset);
        mapping->insert({call_inst, offset});
        // cerr << inst->get_name() << " -- " << offset << endl;
    }
    return asm_code;
}
string CodeGen::generateGlobalVarsCode() {
    GOT.clear();
    string asm_code;
    // TODO: Generate Global Variables
    for (auto &x : this->module->get_global_variable()) {
        auto var_name = x->get_name();
        if (auto const_str =
                dynamic_cast<lightir::ConstantStr *>(x->get_init());
            const_str) {
            asm_code += "\n";
            asm_code += fmt::format(".globl ${}\n", var_name);
            asm_code += fmt::format("${}:\n", var_name);
            asm_code += "  .word 3\n";
            asm_code += "  .word 5\n";
            asm_code += "  .word $str$dispatchTable\n";
            asm_code +=
                fmt::format("  .word {}\n", const_str->get_value().length());
            asm_code += fmt::format("  .word $str.{}\n", var_name);
            asm_code += "\n";

            asm_code += fmt::format(".globl $str.{}\n", var_name);
            asm_code += fmt::format("$str.{}:\n", var_name);
            string str_data;
            for (auto &x : const_str->get_value()) {
                str_data += fmt::format("\\x{:02x}", int(x));
            }
            // asm_code +=
            //     fmt::format("  .asciz \"{}\"\n", const_str->get_value());
            asm_code += fmt::format("  .asciz \"{}\"\n", str_data);
            asm_code += "\n";

            global_map.insert({var_name, "$" + var_name});
        } else {
            int init_val = 0;
            if (auto const_int =
                    dynamic_cast<lightir::ConstantInt *>(x->get_init())) {
                init_val = const_int->get_value();
            }
            asm_code += fmt::format(".globl ${}\n", var_name);
            asm_code += fmt::format("${}:\n", var_name);
            asm_code += fmt::format("  .word {}\n", to_string(init_val));

            global_map.insert({var_name, "$" + var_name});
        }
    }
    return asm_code;
}
string CodeGen::generateInitializerCode(Constant *init) {
    string asm_code;
    // TODO: Generate Constant

    return asm_code;
}

string CodeGen::stackToReg(InstGen::Addr addr, InstGen::Reg reg) {
    if (-2048 <= addr.getOffset() && addr.getOffset() < 2048) {
        return backend->emit_lw(reg, addr.getReg(), addr.getOffset());
    } else {
        string asm_code;
        const auto t0 = InstGen::Reg("t0");
        asm_code += backend->emit_li(t0, addr.getOffset());
        asm_code += backend->emit_add(t0, addr.getReg(), t0);
        asm_code += backend->emit_lw(reg, t0, 0);
        return asm_code;
    }
}
string CodeGen::regToStack(InstGen::Reg reg, InstGen::Addr addr) {
    if (-2048 <= addr.getOffset() && addr.getOffset() < 2048) {
        return backend->emit_sw(reg, addr.getReg(), addr.getOffset());
    } else {
        string asm_code;
        const auto t0 = InstGen::Reg("t0");
        asm_code += backend->emit_li(t0, addr.getOffset());
        asm_code += backend->emit_add(t0, addr.getReg(), t0);
        asm_code += backend->emit_sw(reg, t0, 0);
        return asm_code;
    }
}

pair<int, bool> CodeGen::getConstIntVal(Value *val) {
    auto const_val = dynamic_cast<ConstantInt *>(val);
    auto inst_val = dynamic_cast<Instruction *>(val);
    if (const_val) {
        return std::make_pair(const_val->get_value(), true);
    } else if (inst_val) {
        auto op_list = inst_val->get_operands();
        if (dynamic_cast<BinaryInst *>(val)) {
            auto val_0 = CodeGen::getConstIntVal(op_list.at(0));
            auto val_1 = CodeGen::getConstIntVal(op_list.at(1));
            if (val_0.second && val_1.second) {
                int ret = 0;
                bool flag = true;
                switch (inst_val->get_instr_type()) {
                    case Instruction::Add:
                        ret = val_0.first + val_1.first;
                        break;
                    case Instruction::Sub:
                        ret = val_0.first - val_1.first;
                        break;
                    case Instruction::And:
                        ret = val_0.first & val_1.first;
                        break;
                    case Instruction::Or:
                        ret = val_0.first | val_1.first;
                        break;
                    case Instruction::Mul:
                        ret = val_0.first * val_1.first;
                        break;
                    case Instruction::Div:
                        ret = val_0.first / val_1.first;
                        break;
                    case Instruction::Rem:
                        ret = val_0.first % val_1.first;
                        break;
                    default:
                        flag = false;
                        break;
                }
                return std::make_pair(ret, flag);
            } else {
                return std::make_pair(0, false);
            }
        }
        if (dynamic_cast<UnaryInst *>(val)) {
            auto val_0 = CodeGen::getConstIntVal(op_list.at(0));
            if (val_0.second) {
                int ret = 0;
                bool flag = true;
                switch (inst_val->get_instr_type()) {
                    case Instruction::Not:
                        ret = !val_0.first;
                        break;
                    case Instruction::Neg:
                        ret = -val_0.first;
                        break;
                    default:
                        flag = false;
                        break;
                }
                return std::make_pair(ret, flag);
            } else {
                return std::make_pair(0, false);
            }
        }
    } else if (dynamic_cast<ConstantNull *>(val)) {
        return std::make_pair(0, true);
    }
    LOG(ERROR) << "Function getConstIntVal exception!";
    exit(EXIT_FAILURE);
}
string CodeGen::comment(const string &s) {
    std::string asm_code;
    asm_code += fmt::format("# {}\n", s);
    return asm_code;
}
string CodeGen::comment(const string &t, const string &s) {
    std::string asm_code;
    asm_code += fmt::format("{:<42}{:<42}\n", t, fmt::format("# {}", s));
    return asm_code;
}
}  // namespace cgen

#ifdef PA4
int main(int argc, char *argv[]) {
    string target_path;
    string input_path;

    bool emit = false;
    bool run = false;
    bool assem = false;

    for (int i = 1; i < argc; ++i) {
        if (argv[i] == "-h"s || argv[i] == "--help"s) {
            print_help(argv[0]);
            return 0;
        } else if (argv[i] == "-o"s) {
            if (target_path.empty() && i + 1 < argc) {
                target_path = argv[i + 1];
                i += 1;
            } else {
                print_help(argv[0]);
                return 0;
            }
        } else if (argv[i] == "-emit"s) {
            emit = true;
        } else if (argv[i] == "-assem"s) {
            assem = true;
        } else if (argv[i] == "-run"s) {
            run = true;
        } else {
            if (input_path.empty()) {
                input_path = argv[i];
                if (target_path.empty())
                    target_path = replace_all(input_path, ".py", "");
            } else {
                print_help(argv[0]);
                return 0;
            }
        }
    }

    std::unique_ptr<parser::Program> tree(parse(input_path.c_str()));
    if (tree->errors->compiler_errors.size() != 0) {
        cout << "Syntax Error" << endl;
        return 0;
    }

    auto symboltableGenerator = semantic::SymbolTableGenerator(*tree);
    tree->accept(symboltableGenerator);
    if (tree->errors->compiler_errors.size() == 0) {
        auto typeChecker = semantic::TypeChecker(*tree);
        tree->accept(typeChecker);
    }

    if (tree->errors->compiler_errors.size() != 0) {
        cout << "Type Error" << endl;
        return 0;
    }

    std::shared_ptr<lightir::Module> m;
    auto LightWalker = lightir::LightWalker(*tree);
    light_walker = &LightWalker;
    tree->accept(LightWalker);
    m = LightWalker.get_module();
    m->source_file_name_ = input_path;

    string IR = fmt::format(
        "; ModuleID = \"{}\"\n"
        "source_filename = \"{}\"\n"
        "{}",
        m->module_name_, m->source_file_name_, m->print());

    std::ofstream output_stream(target_path + ".ll");
    output_stream << IR;
    output_stream.flush();

    if (emit) {
        cout << IR;
    }

    cgen::CodeGen code_generator(m);
    string asm_code = code_generator.generateModuleCode();

    std::ofstream output_stream1(target_path + ".s");
    output_stream1 << asm_code;
    output_stream1.flush();

    if (assem) {
        cout << asm_code;
    }

    if (run) {
        auto generate_exec = fmt::format(
            "riscv64-elf-gcc -mabi=ilp32 -march=rv32imac -g "
            "-o {} {}.s "
            "-L./ -L./build -L../build -lchocopy_stdlib",
            target_path, target_path);
        int re_code_0 = std::system(generate_exec.c_str());

        auto qemu_run = fmt::format("qemu-riscv32 {}", target_path);
        int re_code_1 = std::system(qemu_run.c_str());
    }
    return 0;
}
#endif
