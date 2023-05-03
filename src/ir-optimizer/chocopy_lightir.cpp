#include "chocopy_lightir.hpp"

#include <cassert>
#include <exception>
#include <fstream>
#include <ranges>
#include <regex>
#include <string>
#include <type_traits>
#include <utility>

#include "BasicBlock.hpp"
#include "Class.hpp"
#include "ClassDefType.hpp"
#include "Constant.hpp"
#include "Function.hpp"
#include "FunctionDefType.hpp"
#include "GlobalVariable.hpp"
#include "IRBuilder.hpp"
#include "Module.hpp"
#include "SymbolType.hpp"
#include "Type.hpp"
#include "Value.hpp"
#include "ValueType.hpp"
#include "chocopy_parse.hpp"
#include "chocopy_semant.hpp"

namespace lightir {
#define CONST(num) ConstantInt::get(num, &*module)

int LightWalker::get_next_type_id() { return next_type_id++; }
int LightWalker::get_const_type_id() { return next_const_id++; }

string LightWalker::get_fully_qualified_name(semantic::FunctionDefType *func) {
    // TODO: FQN
    // check ChocoPy v2.2: RISC-V Implementation Guide 2.Naming conventions
    return "";
}

/*
 * Convert
 *       Type:
 *           "int"  -> "i32"
 *           "bool" -> "i1"
 *           "str"  -> ptr_str_type
 *           "<None>" -> ptr_obj_type
 *           USER_CLASS to ptr_to_USER_CLASS
 *       *GLOBAL* Function:
 *           FunctionDef  ->  FuntcionType
 */
Type *LightWalker::semantic_type_to_llvm_type(semantic::SymbolType *type) {
    if (type->is_list_type()) {
        return PtrType::get(list_class);
    } else if (dynamic_cast<semantic::ClassValueType *>(type)) {
        if (type->get_name() == "int") {
            return i32_type;
        } else if (type->get_name() == "bool") {
            return i1_type;
        } else if (type->get_name() == "str") {
            return ptr_str_type;
        } else if (type->get_name() == "<None>") {
            return ptr_obj_type;
        } else {
            const auto class_ =
                dynamic_cast<Class *>(scope.find_in_global(type->get_name()));
            assert(class_);
            return PtrType::get(class_);
        }
    } else if (type->is_func_type()) {
        // only support global function
        const auto func_def_type =
            dynamic_cast<semantic::FunctionDefType *>(type);
        std::vector<Type *> arg_types;
        for (auto param : func_def_type->params) {
            arg_types.emplace_back(semantic_type_to_llvm_type(param.get()));
        }
        auto func_return_type =
            semantic_type_to_llvm_type(func_def_type->return_type.get());
        auto func_type = FunctionType::get(func_return_type, arg_types);
        return func_type;
    }
    assert(0);
}

/*
 *   sym: Symbol Table
 *   Setting up pre-defined types:
 *       void, i32, i1, i8, ptr_i8_type
 */
LightWalker::LightWalker(parser::Program &program)
    : sym(&program.symbol_table) {
    module = std::make_unique<Module>("ChocoPy code");
    builder = std::make_unique<IRBuilder>(nullptr, module.get());

    // *  Setting up pre-defined types:
    // *      void, i32, i1, i8, ptr_i8_type
    void_type = Type::get_void_type(&*module);
    i32_type = Type::get_int32_type(&*module);
    i1_type = Type::get_int1_type(&*module);
    i8_type = IntegerType::get(8, &*module);
    ptr_i8_type = PtrType::get(i8_type);

    // *  Object Class & ptr_obj_type
    object_class = new Class(&*module, "object", 0, nullptr, true, true);
    ptr_obj_type = PtrType::get(object_class->get_type());

    // *  Null
    null = ConstantNull::get(ptr_obj_type);

    // *  initializer for Object Class
    auto object_init =
        Function::create(FunctionType::get(ptr_obj_type, {ptr_obj_type}),
                         "$object.__init__", &*module);
    object_class->add_method(object_init);

    // * ptr_ptr_obj_type
    ptr_ptr_obj_type = PtrType::get(ptr_obj_type);

    /*
     * Int Class
     * ptr_int_type
     * Int.__init__()
     * Int.__int__
     */
    int_class = new Class(&*module, "int", 1, nullptr, true, true);
    ptr_int_type = PtrType::get(int_class->get_type());
    int_class->add_method(object_init);
    int_class->add_attribute(new AttrInfo(i32_type, "__int__"));

    /*
     * Bool Class
     * ptr_bool_type
     * Bool.__init__()
     * Bool.__bool__
     */
    bool_class = new Class(&*module, "bool", 2, nullptr, true, true);
    ptr_bool_type = PtrType::get(bool_class->get_type());
    bool_class->add_method(object_init);
    bool_class->add_attribute(new AttrInfo(i1_type, "__bool__"));

    /*
     * Str Class
     * ptr_str_type
     * Str.__init__()
     * Str.__len__
     * Str.__str__
     */
    Class *str_class = new Class(module.get(), "str", 3, object_class, true);
    str_class->add_attribute(new AttrInfo(i32_type, "__len__", 0));
    str_class->add_attribute(new AttrInfo(ptr_i8_type, "__str__"));
    str_class->add_method(object_init);
    ptr_str_type = PtrType::get(str_class->get_type());

    /*
     * List Class
     * List.__init__()
     * List.__len__
     * List.__list__
     */
    list_class = new Class(&*module, ".list", -1, nullptr, true);
    list_class->add_method(object_init);
    list_class->add_attribute(new AttrInfo(i32_type, "__len__", 0));
    list_class->add_attribute(new AttrInfo(ptr_ptr_obj_type, "__list__", 0));

    // * ptr_list_type
    auto TyListClass = list_class->get_type();
    ptr_list_type = PtrType::get(TyListClass);

    // * Predefined functions.
    // * print OOB (Out Of Bound) error and exit
    error_oob_fun = Function::create(FunctionType::get(void_type, {}),
                                     "error.OOB", module.get());

    // * print None error and exit
    error_none_fun = Function::create(FunctionType::get(void_type, {}),
                                      "error.None", module.get());

    // * print Div Zero error and exit
    error_div_fun = Function::create(FunctionType::get(void_type, {}),
                                     "error.Div", module.get());

    /*
     *   param:
     *       number of elements,
     *       element, element, ... (variable args)
     *   return:
     *       pointer to a list
     */
    construct_list_fun = Function::create(
        FunctionType::get(ptr_list_type, {i32_type, i32_type}, true),
        "construct_list", module.get());

    /*
     *   param:
     *       pointer to a list,
     *       pointer to a list
     *   return:
     *       pointer to a new list
     */
    concat_fun = Function::create(
        FunctionType::get(ptr_list_type, {ptr_list_type, ptr_list_type}),
        "concat_list", module.get());

    /*
     *   param:
     *        char
     *   return:
     *        pointer to a str object
     */
    makestr_fun = Function::create(FunctionType::get(ptr_str_type, {i8_type}),
                                   "makestr", module.get());

    /*
     *   param:
     *       pointer to an object
     *   return:
     *       length of the object
     */
    len_fun = Function::create(FunctionType::get(i32_type, {ptr_obj_type}),
                               "$len", module.get());

    /*
     *   param:
     *       pointer to an object
     */
    print_fun = Function::create(FunctionType::get(void_type, {ptr_obj_type}),
                                 "print", module.get());

    /*
     *   param:
     *       pointer to object
     *   return:
     *       pointer to a new object with the same type
     */
    alloc_fun =
        Function::create(FunctionType::get(ptr_obj_type, {ptr_obj_type}),
                         "alloc_object", module.get());

    /*
     *   param:
     *       bool value
     *   return:
     *       pointer to a bool object
     */
    makebool_fun = Function::create(FunctionType::get(ptr_bool_type, {i1_type}),
                                    "makebool", module.get());

    /*
     *  param:
     *      int value
     *  return:
     *      pointer to a int object
     */
    makeint_fun = Function::create(FunctionType::get(ptr_int_type, {i32_type}),
                                   "makeint", module.get());

    //* return: pointer to a str object
    input_fun = Function::create(FunctionType::get(ptr_str_type, {}), "$input",
                                 module.get());

    /*
     *  param:
     *      pointer to str object, pointer to str object
     *  return:
     *      bool
     */
    auto str_compare_type =
        FunctionType::get(i1_type, {ptr_str_type, ptr_str_type});
    streql_fun =
        Function::create(str_compare_type, "str_object_eq", module.get());
    strneql_fun =
        Function::create(str_compare_type, "str_object_neq", module.get());

    /*
     *  param:
     *      pointer to str object, pointer to str object
     *  return:
     *      pointer to a new str object
     */
    strcat_fun = Function::create(
        FunctionType::get(ptr_str_type, {ptr_str_type, ptr_str_type}),
        "str_object_concat", module.get());

    // * Enter the Global scope and install pre-defined Classes
    scope.enter();
    scope.push_in_global("object", object_class);
    scope.push_in_global("int", int_class);
    scope.push_in_global("bool", bool_class);
    scope.push_in_global("str", str_class);
    scope.push_in_global(".list", list_class);
}

// Useless visitors
void LightWalker::visit(parser::Errors &) { assert(0); };
void LightWalker::visit(parser::Node &) { assert(0); };
void LightWalker::visit(parser::TypeAnnotation &) { assert(0); }
void LightWalker::visit(parser::TypedVar &) { assert(0); }
void LightWalker::visit(parser::PassStmt &) {}
void LightWalker::visit(parser::GlobalDecl &) {}
void LightWalker::visit(parser::NonlocalDecl &) {}

string get_unique_func_name(semantic::FunctionDefType *func_def_type) {
    auto parent_sym = func_def_type->current_scope.parent;
    auto parent_parent_sym = parent_sym->parent;
    // 1. global->function
    if (!parent_parent_sym) {
        return "$" + func_def_type->get_name();
    }
    // 2. global->class->method
    for (auto &e : parent_parent_sym->tab) {
        auto parent_class =
            dynamic_cast<semantic::ClassDefType *>(e.second.get());
        if (parent_class && &(parent_class->current_scope) == parent_sym) {
            return "$" + parent_class->class_name + "." +
                   func_def_type->get_name();
        }
    }
}

/*
 * Analyze PROGRAM, creating Info objects for all symbols.
 * Populate the global symbol table.
 */
void LightWalker::visit(parser::Program &node) {
    // * setup main
    auto main_func_type = FunctionType::get(void_type, {});
    auto main_func = Function::create(main_func_type, "main", module.get());

    // * Create main_basic_block;
    auto main_bb = BasicBlock::create(&*module, "", main_func);

    // * Set insert point and install main to Global
    builder->set_insert_point(main_bb);
    scope.push_in_global("$main", main_func);

    // TODO: maybe you have to add/modifiy some code here, it is up to you
    for (const auto &decl : node.declarations) {
        if (auto func_def = dynamic_cast<parser::FuncDef *>(decl.get());
            func_def) {
            // Semantic type
            auto func_semantic_type =
                sym->declares<semantic::FunctionDefType>(func_def->name->name);

            // FunctionType
            auto global_func_llvm_type = dynamic_cast<FunctionType *>(
                semantic_type_to_llvm_type(func_semantic_type));

            // global_func_name
            auto global_func_name = get_unique_func_name(func_semantic_type);

            // func
            auto func = Function::create(global_func_llvm_type,
                                         global_func_name, module.get());
            // scope.push_in_global(func_def->name->name, func);
            scope.push_in_global(global_func_name, func);
        } else {
            decl->accept(*this);
        }
    }
    for (const auto &decl : node.declarations) {
        if (dynamic_cast<parser::FuncDef *>(decl.get())) {
            decl->accept(*this);
        }
    }
    for (const auto &stmt : node.statements) {
        stmt->accept(*this);
    }

    // no need to change the code below
    for (auto &func : this->module->get_functions()) {
        func->set_instr_name();
    }

    builder->create_asm(
        "li a0, 0 \\0A"
        "li a7, 93 #exit system call\\0A"
        "ecall");
    builder->create_void_ret();
}

void LightWalker::visit(parser::ExprStmt &node) { node.expr->accept(*this); }
void LightWalker::visit(parser::IntegerLiteral &node) {
    auto C = CONST(node.value);
    visitor_return_value = C;
}
void LightWalker::visit(parser::BoolLiteral &node) {
    auto C = CONST(node.bin_value);
    visitor_return_value = C;
}
void LightWalker::visit([[maybe_unused]] parser::NoneLiteral &node) {
    visitor_return_value = null;
}

void LightWalker::visit(parser::AssignStmt &node) {
    // TODO: Implement this
    node.value->accept(*this);
    auto value = visitor_return_value;
    for (auto &target : node.targets) {
        get_lvalue = true;
        target->accept(*this);
        get_lvalue = false;
        auto addr = visitor_return_value;
        if (node.value->inferredType->get_name() == "int") {
            if (target->inferredType->get_name() == "int") {
                builder->create_store(value, addr);
            } else {
                auto int_object = builder->create_call(makeint_fun, {value});
                builder->create_store(int_object, addr);
            }
        } else if (node.value->inferredType->get_name() == "bool") {
            if (target->inferredType->get_name() == "bool") {
                builder->create_store(value, addr);
            } else {
                auto bool_object = builder->create_call(makebool_fun, {value});
                builder->create_store(bool_object, addr);
            }
        } else if (node.value->inferredType->get_name() == "str") {
            builder->create_store(value, addr);
        } else {
            builder->create_store(value, addr);
        }
        // TODO Class
    }
}
void LightWalker::visit(parser::BinaryExpr &node) {
    // TODO: Implement this, this is not complete
    Instruction *result;
    node.left->accept(*this);
    auto v1 = this->visitor_return_value;
    node.right->accept(*this);
    auto v2 = this->visitor_return_value;
    if (node.operator_ == "+") {
        if (node.left->inferredType->get_name() == "int") {
            result = builder->create_iadd(v1, v2);
        } else if (node.left->inferredType->get_name() == "str") {
            result = builder->create_call(strcat_fun, {v1, v2});
            result->set_type(ptr_str_type);
        } else {
            result = builder->create_call(concat_fun, {v1, v2});
        }
    } else if (node.operator_ == "==") {
        if (node.left->inferredType->get_name() == "int") {
            result = builder->create_icmp_eq(v1, v2);
        } else if (node.left->inferredType->get_name() == "str") {
            result = builder->create_call(streql_fun, {v1, v2});
            result->set_type(ptr_str_type);
        } else {
            auto zext_int_1 = builder->create_zext(v1, i32_type);
            auto zext_int_2 = builder->create_zext(v2, i32_type);
            result = builder->create_icmp_eq(zext_int_1, zext_int_2);
        }
    } else if (node.operator_ == "!=") {
        if (node.left->inferredType->get_name() == "int") {
            result = builder->create_icmp_ne(v1, v2);
        } else if (node.left->inferredType->get_name() == "str") {
            result = builder->create_call(strneql_fun, {v1, v2});
            result->set_type(ptr_str_type);
        } else {
            auto zext_int_1 = builder->create_zext(v1, i32_type);
            auto zext_int_2 = builder->create_zext(v2, i32_type);
            result = builder->create_icmp_ne(zext_int_1, zext_int_2);
        }
    } else if (node.operator_ == "*") {
        result = builder->create_imul(v1, v2);
    } else if (node.operator_ == "-") {
        result = builder->create_isub(v1, v2);
    } else if (node.operator_ == "//") {
        result = builder->create_isdiv(v1, v2);
    } else if (node.operator_ == "%") {
        result = builder->create_irem(v1, v2);
    } else if (node.operator_ == "and" || node.operator_ == "or") {
        // ! TODO: short circuit
    } else if (node.operator_ == ">") {
        result = builder->create_icmp_gt(v1, v2);
    } else if (node.operator_ == ">=") {
        result = builder->create_icmp_ge(v1, v2);
    } else if (node.operator_ == "<") {
        result = builder->create_icmp_lt(v1, v2);
    } else if (node.operator_ == "<=") {
        result = builder->create_icmp_le(v1, v2);
    } else if (node.operator_ == "is") {
        result = builder->create_icmp_eq(v1, v2);
    } else {
        assert(false);
    }
    visitor_return_value = result;
}
void LightWalker::visit(parser::CallExpr &node) {
    // TODO: Implement this, this is not complete
    const auto &func_name = node.function->name;
    if (func_name == "print") {
        node.args.at(0)->accept(*this);
        auto v1 = this->visitor_return_value;
        if (node.args.at(0)->inferredType->get_name() == "int") {
            auto t = builder->create_call(makeint_fun, {v1});
            builder->create_call(print_fun, {t});
        } else if (node.args.at(0)->inferredType->get_name() == "bool") {
            auto t = builder->create_call(makebool_fun, {v1});
            builder->create_call(print_fun, {t});
        } else {
            builder->create_call(print_fun, {v1});
        }
    } else if (func_name == "len") {
        // ! Now only support str
        node.args.at(0)->accept(*this);
        auto v1 = this->visitor_return_value;
        auto ret_val = builder->create_call(len_fun, {v1});
        visitor_return_value = ret_val;
    } else if (func_name == "int" || func_name == "bool") {
        visitor_return_value = CONST(0);
    } else {
        // is Global function ?
        auto func =
            dynamic_cast<Function *>(scope.find_in_global("$" + func_name));
        vector<Value *> arg_list;
        for (auto &arg : node.args) {
            arg->accept(*this);
            arg_list.push_back(visitor_return_value);
        }
        if (func) {
            // Global function
            visitor_return_value = builder->create_call(func, arg_list);
        } else {
            // Class initialization
            auto class_prototype =
                dynamic_cast<Class *>(scope.find_in_global(func_name));
            visitor_return_value =
                builder->create_call(alloc_fun, {class_prototype});
            auto init_func = class_prototype->get_method()->at(0);
            builder->create_call(init_func, {visitor_return_value});
        }
    }
}
void LightWalker::visit(parser::ClassDef &node) {
    // TODO: Implement this
    auto class_def = sym->get<semantic::ClassDefType>(node.name->name);
    auto super_class_def =
        sym->get<semantic::ClassDefType>(node.superClass->name);

    auto prev_sym = sym;
    sym = &class_def->current_scope;
    // search for super class
    Class *super_class = nullptr;
    for (auto &class_defined : module->get_class()) {
        if (class_defined->name_ == node.superClass->name) {
            super_class = class_defined;
        }
    }
    // current class
    auto current_class = new Class(module.get(), node.name->name,
                                   get_next_type_id(), super_class);
    // install current class
    scope.push(node.get_id()->name, current_class);

    // add super class attributes
    for (auto &attr : *super_class->get_attribute()) {
        current_class->add_attribute(attr);
    }
    // add super class method
    for (auto &method : *super_class->get_method()) {
        current_class->add_method(method);
    }
    // Attributes first
    for (auto &decl : node.declaration) {
        if (auto var_def = dynamic_cast<parser::VarDef *>(decl.get());
            var_def) {
            auto attr_name = var_def->get_id()->name;
            if (super_class_def->current_scope.declares(attr_name)) continue;

            dynamic_cast<::parser::ClassType *>(var_def->var->type.get())
                ->accept(*this);
            auto var_type = visitor_return_type;
            AttrInfo *attr = nullptr;
            if (var_type->is_integer_type()) {
                attr = new AttrInfo(var_type, attr_name,
                                    var_def->value->int_value);
            } else if (var_type->is_bool_type()) {
                attr = new AttrInfo(
                    var_type, attr_name,
                    dynamic_cast<parser::BoolLiteral *>(var_def->value.get())
                        ->bin_value);
            } else if (var_type == ptr_str_type) {
                dynamic_cast<parser::StringLiteral *>(var_def->value.get())
                    ->accept(*this);
                attr = new AttrInfo(var_type, attr_name, visitor_return_value);
            } else {
                attr = new AttrInfo(var_type, attr_name);
            }
            current_class->add_attribute(attr);
        }
    }
    // (override) methods
    for (auto &decl : node.declaration) {
        if (auto func_def = dynamic_cast<parser::FuncDef *>(decl.get());
            func_def) {
            auto func_name = func_def->get_id()->name;
            auto func_def_type =
                sym->declares<semantic::FunctionDefType>(func_name);
            auto func_llvm_type = dynamic_cast<FunctionType *>(
                semantic_type_to_llvm_type(func_def_type));

            auto func = Function::create(
                func_llvm_type, "$" + node.get_id()->name + "." + func_name,
                module.get());
            // scope.push_in_global(func_name, func);
            scope.push_in_global("$" + node.get_id()->name + "." + func_name,
                                 func);
            current_class->add_method(func);
        }
    }
    for (auto &decl : node.declaration) {
        if (auto func_def = dynamic_cast<parser::FuncDef *>(decl.get());
            func_def) {
            func_def->accept(*this);
            // TODO : method in FuncDef
        }
    }
    sym = prev_sym;
}
void LightWalker::visit(parser::ClassType &node) {
    // TODO: Implement this
    if (node.className == "int") {
        visitor_return_type = i32_type;
    } else if (node.className == "bool") {
        visitor_return_type = i1_type;
    } else if (node.className == "str") {
        visitor_return_type = ptr_str_type;
    } else {
        auto contained_class =
            dynamic_cast<Class *>(scope.find_in_global(node.className));
        visitor_return_type = PtrType::get(contained_class);
    }
}
void LightWalker::visit(parser::ForStmt &node) {
    // TODO: Implement this
}

void LightWalker::visit(parser::FuncDef &node) {
    // TODO: Implement this
    // Semantic type
    auto func_semantic_type =
        sym->declares<semantic::FunctionDefType>(node.name->name);

    // FunctionType
    auto global_func_llvm_type = dynamic_cast<FunctionType *>(
        semantic_type_to_llvm_type(func_semantic_type));

    // TODO method
    // global_func_name
    auto global_func_name = get_unique_func_name(func_semantic_type);

    // func
    // auto func = dynamic_cast<Function
    // *>(scope.find_in_global(node.name->name));
    auto func =
        dynamic_cast<Function *>(scope.find_in_global(global_func_name));

    // basic blocks
    auto prev_basic_block = builder->get_insert_block();
    auto new_basic_block = BasicBlock::create(module.get(), "", func);
    builder->set_insert_point(new_basic_block);

    auto prev_sym = sym;
    sym = &func_semantic_type->current_scope;

    scope.enter();

    for (int i = 0; i < node.params.size(); ++i) {
        auto &param = node.params[i];
        auto param_semantic_type = sym->declares(param->identifier->name);
        auto param_llvm_type = semantic_type_to_llvm_type(param_semantic_type);
        auto param_ptr = builder->create_alloca(param_llvm_type);
        scope.push(param->identifier->name, param_ptr);
        builder->create_store(new Value(param_llvm_type, "arg" + to_string(i)),
                              param_ptr);
    }

    for (auto &decl : node.declarations) {
        decl->accept(*this);
    }

    for (auto &stmt : node.statements) {
        stmt->accept(*this);
    }
    // return none
    // if () {
    if (!node.returnType || (node.returnType->get_name() != "int" &&
                             node.returnType->get_name() != "bool"))
        builder->create_ret(new ConstantNull(func->get_return_type()));
    // }
    builder->set_insert_point(prev_basic_block);
    scope.exit();
    sym = prev_sym;
}
void LightWalker::visit(parser::Ident &node) {
    // TODO: Implement this
    auto value = scope.find(node.name);
    assert(value);
    if (get_lvalue) {
        visitor_return_value = value;
    } else {
        visitor_return_value = builder->create_load(value);
    }
}
void LightWalker::visit(parser::IfExpr &node) {
    // TODO: Implement this
}
void LightWalker::visit(parser::ListExpr &node) {
    // TODO: Implement this
    auto element_type =
        dynamic_cast<semantic::ListValueType *>(node.inferredType.get())
            ->element_type;
    auto element_llvm_type = semantic_type_to_llvm_type(element_type.get());
    vector<Value *> arg_list = {CONST(int(node.elements.size()))};
    for (auto &e : node.elements) {
        e->accept(*this);
        if (element_type->get_name() == "int" ||
            element_type->get_name() == "bool")
            visitor_return_value->set_type(i32_type);
        else {
            visitor_return_value =
                builder->create_ptrtoint(visitor_return_value, i32_type);
        }
        arg_list.push_back(visitor_return_value);
    }
    auto list = builder->create_call(construct_list_fun, arg_list);
    visitor_return_value = list;
}
void LightWalker::visit(parser::ListType &node) {
    // TODO: Implement this
}
void LightWalker::visit(parser::MemberExpr &node) {
    // TODO: Implement this
    auto saved_is_lvalue = get_lvalue;
    get_lvalue = false;
    node.object->accept(*this);
    get_lvalue = saved_is_lvalue;
    auto current_func = builder->get_insert_block()->get_parent();
    auto object = visitor_return_value;
    auto cond =
        builder->create_icmp_eq(object, new ConstantNull(object->get_type()));
    auto op_on_none = new BasicBlock(module.get(), "", current_func);
    auto end = new BasicBlock(module.get(), "", current_func);

    builder->create_cond_br(cond, op_on_none, end);
    builder->set_insert_point(op_on_none);
    builder->create_call(error_none_fun, {});
    builder->create_br(end);
    builder->set_insert_point(end);

    auto object_def = dynamic_cast<Class *>(
        scope.find_in_global(node.object->inferredType->get_name()));

    object->set_type(PtrType::get(object_def->type_));
    auto attr_offset = object_def->get_attr_offset(node.member->name);
    if (attr_offset < object_def->get_attribute()->size()) {
        // attribute
        auto attr_ptr = builder->create_gep(object, CONST(attr_offset + 3));

        if (node.inferredType->get_name() == "int")
            attr_ptr->set_type(PtrType::get(i32_type));
        else if (node.inferredType->get_name() == "bool")
            attr_ptr->set_type(PtrType::get(i1_type));
        else if (node.inferredType->get_name() == "str")
            attr_ptr->set_type(ptr_str_type);

        if (get_lvalue)
            visitor_return_value = attr_ptr;
        else
            visitor_return_value = builder->create_load(attr_ptr);
    } else {
        // method
        // dispatch table ptr
        auto dispatch_table_ptr = builder->create_gep(object, CONST(2));

        dispatch_table_ptr->set_type(PtrType::get(PtrType::get(
            LabelType::get(object_def->dispatch_table_label_ + "_type",
                           object_def, object_def->get_module()))));

        auto dispatch_table = builder->create_load(dispatch_table_ptr);

        dispatch_table->set_type(PtrType::get(
            LabelType::get(object_def->dispatch_table_label_ + "_type",
                           object_def, object_def->get_module())));

        auto method_offset = object_def->get_method_offset(node.member->name);

        auto method_ptr =
            builder->create_gep(dispatch_table, CONST(method_offset));
        auto func_type =
            object_def->get_method()->at(method_offset)->get_function_type();
        method_ptr->set_type(PtrType::get(PtrType::get(func_type)));
        auto func = builder->create_load(method_ptr);
        visitor_return_value = func;
        visitor_return_type = func_type;
        visitor_return_object = object;
    }
}
void LightWalker::visit(parser::IfStmt &node) {
    node.condition->accept(*this);
    auto cond = visitor_return_value;
    auto b = builder->get_insert_block();
    auto b_true = BasicBlock::create(module.get(), "", b->get_parent());
    auto b_end = BasicBlock::create(module.get(), "", b->get_parent());
    if (node.el == parser::IfStmt::cond::THEN) {
        builder->create_cond_br(cond, b_true, b_end);
        builder->set_insert_point(b_true);
        for (const auto &stmt : node.thenBody) {
            stmt->accept(*this);
        }
        builder->create_br(b_end);
    } else {
        auto b_false = BasicBlock::create(module.get(), "", b->get_parent());
        builder->create_cond_br(cond, b_true, b_false);
        builder->set_insert_point(b_true);
        for (const auto &stmt : node.thenBody) {
            stmt->accept(*this);
        }
        builder->create_br(b_end);
        builder->set_insert_point(b_false);
        if (node.el == parser::IfStmt::cond::THEN_ELSE) {
            for (const auto &stmt : node.elseBody) {
                stmt->accept(*this);
            }
        } else {
            node.elifBody->accept(*this);
        }
        builder->create_br(b_end);
    }
    builder->set_insert_point(b_end);
}
void LightWalker::visit(parser::MethodCallExpr &node) {
    // TODO: Implement this
    node.method->accept(*this);
    auto func = visitor_return_value;
    auto func_type = visitor_return_type;
    auto object = visitor_return_object;
    vector<Value *> arg_list = {object};
    for (auto &arg : node.args) {
        arg->accept(*this);
        arg_list.push_back(visitor_return_value);
    }
    visitor_return_value = builder->create_call(func, func_type, arg_list);
}
void LightWalker::visit(parser::ReturnStmt &node) {
    // TODO: Implement this
    // return void
    if (!node.value) {
        auto func = builder->create_ret(new ConstantNull(ptr_obj_type));
        return;
    }
    node.value->accept(*this);

    if (node.value->inferredType->get_name() == "bool")
        visitor_return_value->set_type(i1_type);

    builder->create_ret(visitor_return_value);
}
void LightWalker::visit(parser::StringLiteral &node) {
    // TODO: Implement this
    auto const_id = get_const_type_id();
    auto const_str_value = ConstantStr::get(node.value, const_id, module.get());
    auto const_str =
        GlobalVariable::create("const_" + to_string(const_id), module.get(),
                               ptr_str_type, false, const_str_value);
    visitor_return_value = const_str;
}
void LightWalker::visit(parser::UnaryExpr &node) {
    // TODO: Implement this
    Instruction *result;
    node.operand->accept(*this);
    auto var = this->visitor_return_value;
    if (node.operator_ == "-") {
        result = builder->create_ineg(var);
    } else if (node.operator_ == "not") {
        result = builder->create_not(var);
    } else {
        assert(false);
    }
    visitor_return_value = result;
}
void LightWalker::visit(parser::VarDef &node) {
    // TODO: Implement this, this is not complete
    // ! str, Class & local variables
    if (scope.in_global()) {
        GlobalVariable *var = nullptr;
        if (node.var->type->get_name() == "int") {
            var = GlobalVariable::create(
                node.var->identifier->name, module.get(), i32_type, false,
                ConstantInt::get(node.value->int_value, module.get()));
        } else if (node.var->type->get_name() == "bool") {
            auto bool_value =
                dynamic_cast<parser::BoolLiteral *>(node.value.get());
            var = GlobalVariable::create(
                node.var->identifier->name, module.get(), i1_type, false,
                ConstantInt::get(bool_value->bin_value, module.get()));
        } else if (node.var->type->get_name() == "str") {
            node.value->accept(*this);
            auto str_addr = visitor_return_value;
            var = GlobalVariable::create(node.var->identifier->name,
                                         module.get(), ptr_str_type, false,
                                         ConstantNull::get(ptr_str_type));
            builder->create_store(str_addr, var);
        } else if (auto var_type = dynamic_cast<Class *>(
                       scope.find_in_global(node.var->type->get_name()));
                   var_type) {
            // Class
            auto ptr_var_type = PtrType::get(var_type);
            var = GlobalVariable::create(node.var->identifier->name,
                                         module.get(), ptr_var_type, false,
                                         ConstantNull::get(ptr_var_type));
        } else {
            // List
            var = GlobalVariable::create(node.var->identifier->name,
                                         module.get(), ptr_list_type, false,
                                         ConstantNull::get(ptr_list_type));
        }

        scope.push_in_global(node.var->identifier->name, var);
    } else {
        Value *var;
        if (node.var->type->get_name() == "int") {
            var = builder->create_alloca(i32_type);
            builder->create_store(
                ConstantInt::get(node.value->int_value, module.get()), var);
        } else if (node.var->type->get_name() == "bool") {
            auto bool_value =
                dynamic_cast<parser::BoolLiteral *>(node.value.get());
            var = builder->create_alloca(i1_type);
            builder->create_store(
                ConstantInt::get(bool_value->bin_value, module.get()), var);
        } else if (node.var->type->get_name() == "str") {
            node.value->accept(*this);
            auto str_addr = visitor_return_value;
            var = builder->create_alloca(ptr_str_type);
            builder->create_store(str_addr, var);
        } else {
            auto var_type = dynamic_cast<Class *>(
                scope.find_in_global(node.var->type->get_name()));
            auto ptr_var_type = PtrType::get(var_type);
            var = builder->create_alloca(ptr_var_type);
            builder->create_store(ConstantNull::get(ptr_var_type), var);
        }
        scope.push(node.var->identifier->name, var);
        assert(0);
    }
}
void LightWalker::visit(parser::WhileStmt &node) {
    // TODO: Implement this
    // set up basic blocks
    auto prev_basic_block = builder->get_insert_block();
    auto cond =
        BasicBlock::create(module.get(), "", prev_basic_block->get_parent());
    auto body =
        BasicBlock::create(module.get(), "", prev_basic_block->get_parent());
    auto end =
        BasicBlock::create(module.get(), "", prev_basic_block->get_parent());
    // jump to cond
    builder->create_br(cond);
    // cond
    builder->set_insert_point(cond);
    node.condition->accept(*this);
    builder->create_cond_br(visitor_return_value, body, end);
    // body
    builder->set_insert_point(body);
    for (auto &stmt : node.body) {
        stmt->accept(*this);
    }
    builder->create_br(cond);
    // end
    builder->set_insert_point(end);
}
void LightWalker::visit(parser::IndexExpr &node) {
    // TODO: Implement this
    auto saved_is_lvalue = get_lvalue;
    get_lvalue = false;
    // evaluate list
    node.list->accept(*this);
    auto list = visitor_return_value;
    // evaluate index
    node.index->accept(*this);
    auto index = visitor_return_value;
    get_lvalue = saved_is_lvalue;

    auto ptr_array_addr = builder->create_gep(list, CONST(4));
    ptr_array_addr->set_type(ptr_ptr_obj_type);
    auto ptr_array = builder->create_load(ptr_array_addr);
    if (node.inferredType->get_name() == "int" ||
        node.inferredType->get_name() == "bool")
        ptr_array->set_type(PtrType::get(i32_type));
    else if (node.inferredType->get_name() == "str")
        ptr_array->set_type(ptr_i8_type);
    else {
        auto class_name = node.inferredType->get_name();
        auto object = dynamic_cast<Class *>(scope.find_in_global(class_name));
        ptr_array->set_type(PtrType::get(PtrType::get(object)));
    }
    auto element_addr = builder->create_gep(ptr_array, index);
    if (get_lvalue)
        visitor_return_value = element_addr;
    else {
        if (node.inferredType->get_name() == "str") {
            auto char_val = builder->create_load(element_addr);
            visitor_return_value =
                builder->create_call(makestr_fun, {char_val});
        } else {
            visitor_return_value = builder->create_load(element_addr);
        }
    }
}
}  // namespace lightir

void print_help(const string_view &exe_name) {
    std::cout << fmt::format(
                     "Usage: {} [ -h | --help ] [ -o <target-file> ] [ -emit ] "
                     "[ -run ] [ -assem ] <input-file>",
                     exe_name)
              << std::endl;
}

#ifdef PA3
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

    if (emit) {
        cout << IR;
    }

    if (assem || run) {
        auto generate_assem = fmt::format(
            "llc -opaque-pointers -O0 -verify-machineinstrs "
            "-mtriple=riscv32-unknown-elf "
            "-o {}.s {}.ll "
            R"(&& /usr/bin/sed -i 's/.*addrsig.*//g' )"
            "{}.s",
            target_path, target_path, target_path);
        int re_code = std::system(generate_assem.c_str());
        std::cerr << "llc return code: " << re_code << std::endl;
    }

    if (run) {
        auto generate_exec = fmt::format(
            "riscv64-elf-gcc -mabi=ilp32 -march=rv32imac -g "
            "-o {} {}.s "
            "-L./ -L./build -L../build -lchocopy_stdlib",
            target_path, target_path);
        int re_code_0 = std::system(generate_exec.c_str());
        std::cerr << "gcc return code: " << re_code_0 << std::endl;

        auto qemu_run = fmt::format("qemu-riscv32 {}", target_path);
        int re_code_1 = std::system(qemu_run.c_str());
        std::cerr << "qemu return code: " << re_code_1 << std::endl;
    }

    return 0;
}
#endif
