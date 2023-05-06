#include "chocopy_semant.hpp"

#include <fmt/core.h>
#include <fmt/format.h>

#include <algorithm>
#include <cassert>
#include <iterator>
#include <list>
#include <map>
#include <memory>
#include <regex>
#include <set>
#include <utility>

#include "FunctionDefType.hpp"
#include "SymbolType.hpp"
#include "ValueType.hpp"
#include "chocopy_parse.hpp"

// * Pass 1: SymbolTableGenerator
// * In this pass, we only handle these errors :
// * 1. Duplicate declaration in the same scope
// * 2. Bad super class/bad class method/re-define attributes/bad override
// * For other errors in declarations, we leave it to the next pass

namespace semantic {
void SymbolTableGenerator::visit(parser::Program &program) {
    for (const auto &decl : program.declarations) {
        auto id = decl->get_id();
        const auto &name = id->name;

        if (sym->declares(name)) {
            errors->emplace_back(new SemanticError(
                id->location,
                "Duplicate declaration of identifier in same scope: " + name));
            continue;
        }

        return_value = nullptr;
        decl->accept(*this);

        if (return_value == nullptr) continue;
        sym->put(name, return_value);
    }
}
void SymbolTableGenerator::visit(parser::ClassDef &class_def) {
    // TODO: Implement this
    // * Get name of super class and itself
    string super_class_name = class_def.superClass->name;
    string class_name = class_def.name->name;
    // fmt::print("{} {}\n", super_class_name, class_name);

    // * Super class must have been defined previouly && not int, string or bool
    auto super_class_def = global_sym->declares<ClassDefType>(super_class_name);
    if (super_class_def == nullptr || super_class_name == "int" ||
        super_class_name == "str" || super_class_name == "bool") {
        // fmt::print("Needed super class: {}\n", super_class_name);
        errors->emplace_back(new SemanticError(
            class_def.location, "Bad super class: " + super_class_name));
        return;
    }

    hierachy_tree->add_class(class_name, super_class_name);

    // * Create a new ClassDefType, will be returned
    auto class_def_type =
        std::make_shared<ClassDefType>(super_class_name, class_name);

    // * Update current scope's symbol table
    auto saved_sym = sym;
    class_def_type->current_scope.parent = sym;
    sym = &class_def_type->current_scope;
    // * Process declarations
    for (const auto &decl : class_def.declaration) {
        auto id = decl->get_id();
        const auto &name = id->name;

        if (sym->declares(name)) {
            errors->emplace_back(new SemanticError(
                id->location,
                "Duplicate declaration of identifier in same scope: " + name));
            continue;
        }
        // * Bad class methods: first parameter not `self:CLASS`,
        if (decl->kind == "FuncDef") {
            auto method_def = (parser::FuncDef *)decl.get();
            bool error = false;
            if (method_def->params.size() == 0)
                error = true;
            else {
                auto first_param = method_def->params.at(0).get();
                if (first_param->type->get_name() != class_name ||
                    first_param->identifier->name != "self")
                    error = true;
            }
            if (error) {
                errors->emplace_back(new SemanticError(
                    id->location, "Bad class method: " + name));
                continue;
            }
        }

        // * redefine attributes && bad class methods override
        // * 1. Redefine attribute/method (decl not Func)
        // * 2. Bad override: change params except first; change return
        // * type(decl is Func)
        auto super_def = global_sym->declares<ClassDefType>(super_class_name);
        bool error = false;
        if (super_def->current_scope.declares<ValueType>(name)) {
            errors->emplace_back(new SemanticError(
                id->location, "Cannot re-define attribute: " + name));
            error = true;
        } else if (super_def->current_scope.declares<FunctionDefType>(name)) {
            if (decl->kind != "FuncDef") {
                errors->emplace_back(new SemanticError(
                    id->location, "Cannot re-define method: " + name));
                error = true;
            } else {
                auto super_method_def =
                    super_def->current_scope.declares<FunctionDefType>(name);
                auto method_def = (parser::FuncDef *)decl.get();
                const auto &super_params = super_method_def->params;
                const auto &params = method_def->params;
                if ((super_method_def->return_type == nullptr) ^
                    (super_method_def->return_type == nullptr)) {
                    error = true;
                }
                if (super_method_def->return_type != nullptr &&
                    method_def->returnType != nullptr &&
                    super_method_def->return_type->get_name() !=
                        method_def->returnType->get_name()) {
                    error = true;
                }
                if (super_params.size() != params.size())
                    error = true;
                else {
                    for (size_t i = 1; i < params.size(); ++i) {
                        if (params[i]->type->get_name() !=
                            super_params[i].get()->get_name()) {
                            error = true;
                        }
                    }
                }
                if (error) {
                    errors->emplace_back(new SemanticError(
                        id->location, "Bad method override: " + name));
                }
            }
        }
        if (error) continue;
        return_value = nullptr;
        decl->accept(*this);

        if (return_value == nullptr) continue;
        sym->put(name, return_value);
    }
    // * Put inherited attributes/methods to the current symbol table
    // * Or we have to search along the chain of super classes every time,
    // * which is extremely inconvenient in the next pass
    auto super_def = global_sym->declares<ClassDefType>(super_class_name);
    for (const auto &entry : super_def->current_scope.tab) {
        if (sym->declares(entry.first) == nullptr)
            sym->put(entry.first, entry.second);
    }
    return_value = class_def_type;
    sym = saved_sym;
}
void SymbolTableGenerator::visit(parser::FuncDef &func_def) {
    // TODO: Implement this

    // * Create a new FunctionDefType, will be returned
    auto func_def_type = std::make_shared<FunctionDefType>();
    // * Fill in function name and return type
    func_def_type->func_name = func_def.get_id()->name;
    func_def_type->return_type =
        ValueType::annotate_to_val(func_def.returnType.get());

    // * Update current scope's symbol table
    auto saved_sym = sym;
    func_def_type->current_scope.parent = sym;
    sym = &func_def_type->current_scope;

    // * Put formal parameters to symbol table
    for (const auto &param : func_def.params) {
        auto id = param->identifier.get();
        const auto &name = id->name;
        // * Put parameter's value type into func_def_type->params, even if it
        // * is a duplicate declaration.
        auto param_type = ValueType::annotate_to_val(param->type.get());
        func_def_type->params.emplace_back(param_type);
        if (sym->declares(name)) {
            errors->emplace_back(new SemanticError(
                id->location,
                "Duplicate declaration of identifier in same scope: " + name));
            continue;
        }
        sym->put(name, param_type);
    }
    // * Process declarations
    for (const auto &decl : func_def.declarations) {
        auto id = decl->get_id();
        const auto &name = id->name;

        if (sym->declares(name)) {
            errors->emplace_back(new SemanticError(
                id->location,
                "Duplicate declaration of identifier in same scope: " + name));
            continue;
        }

        return_value = nullptr;
        decl->accept(*this);

        if (return_value == nullptr) continue;
        sym->put(name, return_value);
    }
    // * Return FuncDefType
    sym = saved_sym;
    return_value = func_def_type;
}
void SymbolTableGenerator::visit(parser::VarDef &var_def) {
    return_value = ValueType::annotate_to_val(var_def.var->type.get());
}

// * Pass 2: DeclarationChecker
// * In the previous pass we mainly dealt with the symbols, now we
// * will look into the correctness of these declarations.
// ! This pass has been merged into TypeChecker

// * Pass 3: TypeChecker
// *
void TypeChecker::typeError(parser::Node *node, const string &message) {
    errors->emplace_back(
        std::make_unique<SemanticError>(node->location, message));
    if (!node->has_type_err()) {
        node->typeError = message;
    } else {
        node->typeError += "\t" + message;
    }
}
void TypeChecker::visit(parser::NonlocalDecl &node) {
    // TODO implement this
    auto id = node.get_id();
    auto name = id->name;
    if (sym->is_nonlocal(name)) {
        auto nonlocal_type = sym->get_shared<ValueType>(name);
        sym->put(name, nonlocal_type);
        current_lambda_params->push_back(name);
    } else {
        typeError(&node, fmt::format("No such nonlocal variable: {}", name));
    }
}
void TypeChecker::visit(parser::GlobalDecl &node) {
    // TODO implement this
    auto id = node.get_id();
    auto name = id->name;
    auto global_type = global->declares_shared<ValueType>(name);
    if (global_type) {
        sym->put(name, global_type);
    } else {
        typeError(&node, fmt::format("No such global variable: {}", name));
    }
}
void TypeChecker::visit(parser::Program &program) {
    for (const auto &decl : program.declarations) {
        decl->accept(*this);
    }
    for (const auto &stmt : program.statements) {
        if (stmt->is_return) {
            typeError(stmt.get(),
                      "Return statement cannot appear at the top level");
        } else {
            stmt->accept(*this);
        }
    }
}
void TypeChecker::visit(parser::TypedVar &node) {
    auto name = node.identifier->name;
    if (global->declares<ClassDefType>(name)) {
        typeError(&node, fmt::format("Cannot shadow class name: {}", name));
    }
    auto annotation_type = sym->declares(name);
    while (dynamic_cast<ListValueType *>(annotation_type)) {
        annotation_type =
            ((ListValueType *)annotation_type)->element_type.get();
    }
    auto element_name = annotation_type->get_name();
    auto element_type = global->declares(element_name);
    if (element_type == nullptr) {
        typeError(
            &node,
            fmt::format("Invalid type annotation; there is no class named: {}",
                        element_name));
        return;
    }
}
void TypeChecker::visit(parser::BinaryExpr &node) {
    // TODO: Implement this, this is not complete
    node.left->accept(*this);
    node.right->accept(*this);
    auto left_type = node.left->inferredType;
    auto right_type = node.right->inferredType;
    if (left_type == nullptr || right_type == nullptr) return;
    auto left_name = left_type->get_name();
    auto right_name = right_type->get_name();
    if (node.operator_ == "+") {
        if (left_type->get_name() == "int" && right_type->get_name() == "int") {
            node.inferredType = int_value_type;
            return;
        }
        if (left_name == "str" && right_name == "str") {
            node.inferredType = str_value_type;
            return;
        }
        if (left_type->is_list_type() && right_type->is_list_type()) {
            auto left_list_type =
                dynamic_pointer_cast<ListValueType>(left_type);
            auto right_list_type =
                dynamic_pointer_cast<ListValueType>(right_type);
            node.inferredType =
                std::make_shared<ListValueType>(dynamic_pointer_cast<ValueType>(
                    LCA(left_list_type->element_type,
                        right_list_type->element_type)));
            return;
        }
        typeError(&node,
                  fmt::format("Cannot apply opreator + on types {} and {}",
                              left_type->get_name(), right_type->get_name()));
    }
    if (node.operator_ == "-" || node.operator_ == "*" ||
        node.operator_ == "//" || node.operator_ == "%") {
        if (left_name == "int" && right_name == "int") {
            node.inferredType = int_value_type;
            return;
        }
        typeError(&node,
                  fmt::format("Cannot apply opreator {} on types {} and {}",
                              node.operator_, left_type->get_name(),
                              right_type->get_name()));
    }
    if (node.operator_ == "and" || node.operator_ == "or") {
        if (left_name == "bool" && right_name == "bool") {
            node.inferredType = bool_value_type;
            return;
        }
        typeError(&node,
                  fmt::format("Cannot apply opreator {} on types {} and {}",
                              node.operator_, left_type->get_name(),
                              right_type->get_name()));
    }
    if (node.operator_ == "==" || node.operator_ == "!=") {
        if ((left_name == "int" || left_name == "str" || left_name == "bool") &&
            left_name == right_name) {
            node.inferredType = bool_value_type;
            return;
        }
        typeError(&node,
                  fmt::format("Cannot apply opreator {} on types {} and {}",
                              node.operator_, left_name, right_name));
    }
    if (node.operator_ == "<" || node.operator_ == "<=" ||
        node.operator_ == ">=" || node.operator_ == ">") {
        if (left_name == "int" && left_name == right_name) {
            node.inferredType = bool_value_type;
            return;
        }
        typeError(&node,
                  fmt::format("Cannot apply opreator {} on types {} and {}",
                              node.operator_, left_name, right_name));
    }
    if (node.operator_ == "is") {
        if (left_name != "int" && left_name != "str" && left_name != "bool" &&
            right_name != "int" && right_name != "str" &&
            right_name != "bool") {
            node.inferredType = bool_value_type;
            return;
        }
        typeError(&node,
                  fmt::format("Cannot apply opreator {} on types {} and {}",
                              node.operator_, left_name, right_name));
    }
}
void TypeChecker::visit(parser::BoolLiteral &node) {
    // TODO: Implement this
    node.inferredType = bool_value_type;
}
void TypeChecker::visit(parser::CallExpr &node) {
    // TODO: Implement this
    auto call_name = node.function->name;
    auto call_def = sym->get_shared<SymbolType>(call_name);
    if (dynamic_pointer_cast<FunctionDefType>(call_def)) {
        auto func_def = dynamic_pointer_cast<FunctionDefType>(call_def);
        bool error = false;
        if (func_def->params.size() != node.args.size())
            error = true;
        else {
            for (size_t i = 0; i < func_def->params.size(); ++i) {
                node.args[i]->accept(*this);
                if (!TypeAssign(node.args[i]->inferredType.get(),
                                func_def->params[i].get())) {
                    error = true;
                    break;
                }
            }
        }
        if (error) {
            typeError(&node, fmt::format("Bad function call: {}", call_name));
        } else {
            node.function->inferredType = func_def;
            node.inferredType = func_def->return_type;

            // capture nested functions called
            if (!sym->declares(call_name) && (global->declares(call_name) !=
                                              sym->get<SymbolType>(call_name)))
                if (current_lambda_params)
                    current_lambda_params->push_back(call_name);
        }
    } else if (dynamic_pointer_cast<ClassDefType>(call_def)) {
        node.inferredType =
            std::make_shared<ClassValueType>(call_def->get_name());
    } else {
        typeError(&node, fmt::format("Not a function or class: {}", call_name));
    }
}
void TypeChecker::visit(parser::ExprStmt &node) { node.expr->accept(*this); }
void TypeChecker::visit(parser::ForStmt &node) {
    // TODO: Implement this
    node.identifier->accept(*this);
    node.iterable->accept(*this);
    for (const auto &stmt : node.body) {
        stmt->accept(*this);
    }
    auto id_type = node.identifier->inferredType;
    auto iterable_type = node.iterable->inferredType;
    if (id_type == nullptr || iterable_type == nullptr) {
        return;
    }
    auto id_name = id_type->get_name();
    auto iterable_name = iterable_type->get_name();
    bool error = true;
    if (iterable_name == "str") {
        if (TypeAssign(iterable_type.get(), id_type.get())) {
            error = false;
        }
    } else if (iterable_type->is_list_type()) {
        auto iterable_list_type =
            dynamic_pointer_cast<ListValueType>(iterable_type);
        if (TypeAssign(iterable_list_type->element_type.get(), id_type.get())) {
            error = false;
        }
    }
    if (error) {
        typeError(&node, "Bad ForStmt");
    }
}
void TypeChecker::visit(parser::ClassDef &node) {
    // TODO: Implement this
    auto saved_sym = sym;
    auto name = node.get_id()->name;
    auto class_def_type = sym->declares_shared<ClassDefType>(name);
    sym = &class_def_type->current_scope;
    for (const auto &decl : node.declaration) {
        decl->accept(*this);
    }
    sym = saved_sym;
}
void TypeChecker::visit(parser::FuncDef &node) {
    // TODO: Implement this
    auto saved_sym = sym;
    auto name = node.get_id()->name;
    if (global->declares<ClassDefType>(name)) {
        typeError(&node, fmt::format("Cannot shadow class name: {}", name));
    }
    auto func_def_type = sym->declares_shared<FunctionDefType>(name);

    sym = &func_def_type->current_scope;
    // * R
    // * Save previous return type
    auto saved_return_type = return_type;
    if (func_def_type->return_type.get() == nullptr) {
        func_def_type->return_type = none_value_type;
    }
    return_type = func_def_type->return_type;
    for (const auto &param : node.params) {
        param->accept(*this);
    }

    // set up lambda_params
    auto saved_lambda_params = current_lambda_params;
    // also treat function defs as variables
    vector<string> local_variables;
    vector<string> lambda_variables;
    current_lambda_params = &lambda_variables;

    // parameters are also local variables
    for (const auto &param : node.params) {
        local_variables.push_back(param->identifier->name);
    }

    for (const auto &decl : node.declarations) {
        decl->accept(*this);
        if (dynamic_cast<parser::VarDef *>(decl.get())) {
            local_variables.push_back(decl->get_id()->name);
        }
        if (dynamic_cast<parser::NonlocalDecl *>(decl.get())) {
            current_lambda_params->push_back(decl->get_id()->name);
        }
        if (auto func_def = dynamic_cast<parser::FuncDef *>(decl.get());
            func_def) {
            local_variables.push_back(decl->get_id()->name);
            current_lambda_params->insert(current_lambda_params->end(),
                                          func_def->lambda_params.begin(),
                                          func_def->lambda_params.end());
        }
    }

    bool have_return = false;
    for (const auto &stmt : node.statements) {
        stmt->accept(*this);
        if (stmt->is_return) {
            have_return = true;
        }
    }

    // std::unique & std::set_different requires sets to be sorted
    std::sort(current_lambda_params->begin(), current_lambda_params->end());
    std::sort(local_variables.begin(), local_variables.end());
    current_lambda_params->resize(
        std::distance(current_lambda_params->begin(),
                      std::unique(current_lambda_params->begin(),
                                  current_lambda_params->end())));

    std::set_difference(current_lambda_params->begin(),
                        current_lambda_params->end(), local_variables.begin(),
                        local_variables.end(),
                        std::back_inserter(node.lambda_params));

    if (!TypeAssign(none_value_type.get(), func_def_type->return_type.get()) &&
        !have_return) {
        typeError(&node, "Missing return");
    }
    // * restore return type and symbol table
    return_type = saved_return_type;
    sym = saved_sym;
    current_lambda_params = saved_lambda_params;
}
void TypeChecker::visit(parser::Ident &node) {
    // TODO: Implement this, this is not complete
    std::shared_ptr<SymbolType> type;
    if (is_assign) {
        type = sym->declares_shared<SymbolType>(node.name);
        // ! For example : x[y], and y is inherited implicitly
        is_assign = false;
    } else {
        type = sym->get_shared<SymbolType>(node.name);
    }
    // add by-value capture
    if (!sym->declares(node.name) &&
        (global->declares(node.name) != sym->get<ValueType>(node.name)))
        if (current_lambda_params) current_lambda_params->push_back(node.name);

    if (type == nullptr || dynamic_pointer_cast<FunctionDefType>(type) ||
        dynamic_pointer_cast<ClassDefType>(type)) {
        typeError(&node, fmt::format("Not a variable: {}", node.name));
        node.inferredType = nullptr;
    } else {
        node.inferredType = type;
    }
}
void TypeChecker::visit(parser::IfStmt &node) {
    // TODO: Implement this
    node.condition->accept(*this);
    bool then_return = false;
    for (const auto &stmt : node.thenBody) {
        stmt->accept(*this);
        if (stmt->is_return) then_return = true;
    }
    bool else_return = false;
    for (const auto &stmt : node.elseBody) {
        stmt->accept(*this);
        if (stmt->is_return) else_return = true;
    }
    if (node.elifBody != nullptr) {
        node.elifBody->accept(*this);
        else_return = node.elifBody->is_return;
    }
    node.is_return = then_return && else_return;
    auto cond_type = node.condition->inferredType;
    if (cond_type == nullptr || cond_type->get_name() != "bool") {
        typeError(&node, fmt::format("Bad condition in IfStmt"));
    }
}
void TypeChecker::visit(parser::IfExpr &node) {
    // TODO: Implement this
    node.condition->accept(*this);
    node.thenExpr->accept(*this);
    node.elseExpr->accept(*this);
    auto cond_type = node.condition->inferredType;
    if (cond_type == nullptr || cond_type->get_name() != "bool") {
        typeError(&node, fmt::format("Bad condition in IfExpr"));
    }
    auto then_type = node.thenExpr->inferredType;
    auto else_type = node.elseExpr->inferredType;
    if (then_type != nullptr && else_type != nullptr) {
        node.inferredType = LCA(then_type, else_type);
    }
}
void TypeChecker::visit(parser::IndexExpr &node) {
    // TODO: Implement this
    node.list->accept(*this);
    node.index->accept(*this);
    // fmt::print(">> {} {}\n", node.list->inferredType->get_name(),
    //            node.index->inferredType->get_name());
    if (node.index->inferredType->get_name() != "int") {
        typeError(&node, fmt::format("Index is of non-integer type `{}`",
                                     node.index->inferredType->get_name()));
    } else {
        if (node.list->inferredType->is_list_type()) {
            node.inferredType =
                dynamic_pointer_cast<ListValueType>(node.list->inferredType)
                    ->element_type;
        } else if (node.list->inferredType->get_name() == "str") {
            node.inferredType = str_value_type;
        } else {
            typeError(&node, fmt::format("Cannot index into type `{}`",
                                         node.list->inferredType->get_name()));
        }
    }
}
void TypeChecker::visit(parser::IntegerLiteral &node) {
    node.inferredType = int_value_type;
}
void TypeChecker::visit(parser::ListExpr &node) {
    // TODO: Implement this
    if (node.elements.empty()) {
        node.inferredType = empty_value_type;
    } else {
        shared_ptr<SymbolType> lca_type = nullptr;
        bool error = false;
        for (const auto &element : node.elements) {
            element->accept(*this);
            if (element->inferredType.get() == nullptr) {
                error = true;
                break;
            }
            if (lca_type == nullptr) {
                lca_type = element->inferredType;
            } else {
                lca_type = LCA(lca_type, element->inferredType);
            }
        }
        if (error) return;
        node.inferredType = std::make_shared<ListValueType>(
            dynamic_pointer_cast<ValueType>(lca_type));
    }
}
void TypeChecker::visit(parser::MemberExpr &node) {
    // TODO: Implement this
    node.object->accept(*this);
    if (!node.object->inferredType) {
        return;
    }
    auto class_name = node.object->inferredType->get_name();
    auto member_name = node.member->name;
    auto class_def = global->declares<ClassDefType>(class_name);
    auto member_def = class_def->current_scope.declares_shared(member_name);
    if (member_def == nullptr) {
        typeError(&node, fmt::format("Not a member: {}", member_name));
    } else {
        node.inferredType = member_def;
    }
}
void TypeChecker::visit(parser::MethodCallExpr &node) {
    // TODO: Implement this
    node.method->accept(*this);
    auto method_name = node.method->member->name;
    auto method_def = node.method->inferredType;
    if (method_def == nullptr || !method_def->is_func_type()) {
        typeError(&node, fmt::format("Not a method: {}", method_name));
        return;
    }
    auto func_def = dynamic_pointer_cast<FunctionDefType>(method_def);
    bool error = false;
    if (func_def->params.size() - 1 != node.args.size()) {
        error = true;
    } else {
        for (size_t i = 0; i < node.args.size(); ++i) {
            node.args[i]->accept(*this);
            auto arg_type = node.args[i]->inferredType;
            auto param_type = func_def->params[i + 1];
            if (arg_type == nullptr || param_type == nullptr ||
                !TypeAssign(arg_type.get(), param_type.get())) {
                error = true;
                break;
            }
        }
    }
    if (error) {
        typeError(&node, fmt::format("Bad function call: {}", method_name));
    } else {
        node.inferredType = func_def->return_type;
    }
}
void TypeChecker::visit(parser::NoneLiteral &node) {
    node.inferredType = none_value_type;
}
void TypeChecker::visit(parser::ReturnStmt &node) {
    // TODO: Implement this
    shared_ptr<SymbolType> value_type;
    if (node.value == nullptr) {
        value_type = none_value_type;
    } else {
        node.value->accept(*this);
        value_type = node.value->inferredType;
    }
    if (TypeAssign(value_type.get(), return_type.get())) {
    } else {
        typeError(&node,
                  fmt::format("Expected type `{}`; got type `{}`",
                              return_type->get_name(), value_type->get_name()));
    }
}
void TypeChecker::visit(parser::StringLiteral &node) {
    node.inferredType = str_value_type;
}
void TypeChecker::visit(parser::UnaryExpr &node) {
    // TODO: Implement this
    node.operand->accept(*this);
    auto operand_type = node.operand->inferredType;
    if (operand_type == nullptr) return;
    auto operand_name = operand_type->get_name();
    if (node.operator_ == "-") {
        if (operand_name == "int") {
            node.inferredType = int_value_type;
            return;
        }
        typeError(&node, fmt::format("Cannot apply operator `-` on type `{}`",
                                     operand_name));
    }
    if (node.operator_ == "not") {
        if (operand_name == "bool") {
            node.inferredType = bool_value_type;
            return;
        }
        typeError(&node, fmt::format("Cannot apply operator `not` on type `{}`",
                                     operand_name));
    }
}
void TypeChecker::visit(parser::VarDef &node) {
    // TODO: Implement this
    node.var->accept(*this);
    node.value->accept(*this);
    if (TypeAssign(node.value->inferredType.get(),
                   sym->declares(node.get_id()->name))) {
    } else {
        typeError(&node, fmt::format("Expected type `{}`; got type `{}`",
                                     node.var->type->get_name(),
                                     node.value->inferredType->get_name()));
    }
}
void TypeChecker::visit(parser::WhileStmt &node) {
    // TODO: Implement this
    node.condition->accept(*this);
    for (const auto &stmt : node.body) {
        stmt->accept(*this);
    }
    if (node.condition->inferredType.get() == nullptr ||
        node.condition->inferredType->get_name() != "bool") {
        typeError(&node, "Bad condition in WhileStmt");
    }
}
void TypeChecker::visit(parser::AssignStmt &node) {
    // TODO: Implement this
    node.value->accept(*this);
    if (node.value->inferredType == nullptr) return;
    for (const auto &target : node.targets) {
        is_assign = true;
        target->accept(*this);
        is_assign = false;
        if (target->inferredType.get() == nullptr) continue;
        if (!TypeAssign(node.value->inferredType.get(),
                        target->inferredType.get())) {
            typeError(&node, fmt::format("Expected type `{}`; got type `{}`",
                                         target->inferredType->get_name(),
                                         node.value->inferredType->get_name()));
        }
    }
}
shared_ptr<SymbolType> TypeChecker::LCA(shared_ptr<SymbolType> type_1,
                                        shared_ptr<SymbolType> type_2) {
    auto name_1 = type_1->get_name();
    auto name_2 = type_2->get_name();
    // * type_1=type_2
    if (name_1 == name_2) {
        return make_shared<ClassValueType>(name_1);
    }
    // * Both type_1 and type_2 are not list types
    if (!type_1->is_list_type() && !type_2->is_list_type()) {
        return make_shared<ClassValueType>(
            hierachy_tree->common_ancestor(name_1, name_2));
    }
    // * Only possibility
    return object_value_type;
}
bool TypeChecker::TypeConform(SymbolType *type_1, SymbolType *type_2) {
    auto name_1 = type_1->get_name();
    auto name_2 = type_2->get_name();
    // fmt::print(">>  {} {}\n", name_1, name_2);
    // * T<=T forany T
    if (name_1 == name_2) {
        return true;
    }
    // * [T] <= object
    if (type_1->is_list_type() && name_2 == "object") {
        return true;
    }
    // * <None> <= object
    if (name_1 == "<None>" && name_2 == "object") {
        return true;
    }
    // * <Empty> <= object
    if (name_1 == "<Empty>" && name_2 == "object") {
        return true;
    }
    // * ordinary subtyping
    if (hierachy_tree->is_superclass(name_1, name_2)) {
        return true;
    }
    return false;
}
bool TypeChecker::TypeAssign(SymbolType *type_1, SymbolType *type_2) {
    auto name_1 = type_1->get_name();
    auto name_2 = type_2->get_name();
    // * ordinary subtyping
    if (TypeConform(type_1, type_2)) {
        return true;
    }
    // * type_1 is `<None>` and type_2 is not `int`, `str` or `bool`
    if (name_1 == "<None>" && name_2 != "int" && name_2 != "str" &&
        name_2 != "bool") {
        return true;
    }
    // * type_2 is list type and type_2 is `<Empty>`
    if (type_2->is_list_type() && name_1 == "<Empty>") {
        return true;
    }
    // * type_2 is list type [T] and type_1 is `[<None>]`, where
    // * TypeLeq(<None>,T)==true
    if (type_2->is_list_type() && type_1->is_list_type() &&
        name_1 == "[<None>]") {
        if (TypeAssign(((ListValueType *)type_1)->element_type.get(),
                       ((ListValueType *)type_2)->element_type.get())) {
            return true;
        }
    }
    return false;
}
void TypeChecker::TypeLeqChecker() {
    fmt::print("A B {}\n",
               TypeAssign(global->declares("A"), global->declares("B")));
    fmt::print("B C {}\n",
               TypeAssign(global->declares("B"), global->declares("C")));
    fmt::print("D object {}\n",
               TypeAssign(global->declares("D"), global->declares("object")));
    // printf("%d\n", global->declares("A"));
    // fmt::print("[A] object\n",
    //            TypeAssign(std::make_shared<ListValueType>(
    //                           global->declares_shared<ValueType>("A"))
    //                           .get(),
    //                       global->declares("object")));
}
}  // namespace semantic

#ifdef PA2
int main(int argc, char *argv[]) {
    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " <filename>" << std::endl;
        return 1;
    }
    std::unique_ptr<parser::Program> tree(parse(argv[1]));
    if (tree->errors->compiler_errors.size() == 0) {
        auto symboltableGenerator = semantic::SymbolTableGenerator(*tree);
        tree->accept(symboltableGenerator);
    }
    if (tree->errors->compiler_errors.size() == 0) {
        auto typeChecker = semantic::TypeChecker(*tree);
        tree->accept(typeChecker);
        // typeChecker.TypeLeqChecker();
    }

    auto j = tree->toJSON();
    std::cout << j.dump(2) << std::endl;
}
#endif
