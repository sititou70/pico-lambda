import {
  AST,
  ASTLambda,
  ASTLet,
  ASTVariable,
  getFreshVariableVariant,
  isASTType,
  isSameVariable,
} from "../parser/types";
import { Result, error, ok } from "../utils/Result";

const replaceVariable = <Term extends AST>(
  term: Term,
  from: ASTVariable,
  to: ASTVariable
): Term => {
  switch (term.type) {
    case "Variable": {
      if (isSameVariable(term, from)) {
        return to as typeof term;
      } else {
        return term;
      }
    }
    case "Lambda": {
      return {
        kind: "ast",
        type: "Lambda",
        argument: replaceVariable(term.argument, from, to),
        body: replaceVariable(term.body, from, to),
      } as typeof term satisfies typeof term;
    }
    case "Apply": {
      return {
        kind: "ast",
        type: "Apply",
        operator: replaceVariable(term.operator, from, to),
        operand: replaceVariable(term.operand, from, to),
      } as typeof term satisfies typeof term;
    }
    case "Zero": {
      return term;
    }
    case "Succ": {
      return {
        kind: "ast",
        type: "Succ",
        body: replaceVariable(term.body, from, to),
      } as typeof term satisfies typeof term;
    }
    case "Let": {
      return {
        kind: "ast",
        type: "Let",
        variable: replaceVariable(term.variable, from, to),
        value: replaceVariable(term.value, from, to),
        body: replaceVariable(term.body, from, to),
      } as typeof term satisfies typeof term;
    }
  }
};

const assign = (term: AST, variable: ASTVariable, value: AST): AST => {
  switch (term.type) {
    case "Variable": {
      if (isSameVariable(term, variable)) {
        return value;
      } else {
        return term;
      }
    }
    case "Lambda": {
      // y ≠ x and y ∉ FV(s)
      const fresh_variable: ASTVariable = {
        ...term.argument,
        variant: getFreshVariableVariant(),
      };
      const fresh_lambda: ASTLambda = replaceVariable(
        term,
        term.argument,
        fresh_variable
      );

      return {
        ...fresh_lambda,
        body: assign(fresh_lambda.body, variable, value),
      };
    }
    case "Apply": {
      return {
        ...term,
        operator: assign(term.operator, variable, value),
        operand: assign(term.operand, variable, value),
      };
    }
    case "Zero": {
      return term;
    }
    case "Succ": {
      return {
        ...term,
        body: assign(term.body, variable, value),
      };
    }
    case "Let": {
      // y ≠ x and y ∉ FV(s)
      const fresh_variable: ASTVariable = {
        ...term.variable,
        variant: getFreshVariableVariant(),
      };
      const fresh_let: ASTLet = replaceVariable(
        term,
        term.variable,
        fresh_variable
      );

      return {
        ...fresh_let,
        value: assign(fresh_let.value, variable, value),
        body: assign(fresh_let.body, variable, value),
      };
    }
  }
};

const evaluate1 = (term: AST): Result<AST> => {
  switch (term.type) {
    case "Variable": {
      return error("cannot eval free variable");
    }
    case "Lambda": {
      return error("cannot eval lambda");
    }
    case "Apply": {
      // E-App1
      const evaluated_operator_result = evaluate1(term.operator);
      if (evaluated_operator_result.success)
        return ok({ ...term, operator: evaluated_operator_result.value });

      // E-App2
      const evaluated_operand_result = evaluate1(term.operand);
      if (evaluated_operand_result.success)
        return ok({ ...term, operand: evaluated_operand_result.value });

      // E-AppAbs
      const operator = term.operator;
      if (!isASTType(operator, "Lambda"))
        return error(
          "unexpected error: operator is not lambda, but cannot be evaluated"
        );

      return ok(assign(operator.body, operator.argument, term.operand));
    }
    case "Zero": {
      return error("cannot eval zero");
    }
    case "Succ": {
      // E-Succ
      const evaluated_body_result = evaluate1(term.body);
      if (evaluated_body_result.success)
        return ok({ ...term, body: evaluated_body_result.value });

      return error("cannot eval succ body");
    }
    case "Let": {
      // E-Let
      const evaluated_value_result = evaluate1(term.value);
      if (evaluated_value_result.success)
        return ok({ ...term, value: evaluated_value_result.value });

      // E-LetV
      return ok(assign(term.body, term.variable, term.value));
    }
  }
};

const isValue = (term: AST): boolean => {
  if (isASTType(term, "Lambda")) return true;
  if (isASTType(term, "Zero")) return true;
  if (isASTType(term, "Succ") && isValue(term.body)) return true;
  return false;
};

export const evaluate = (term: AST): Result<AST> => {
  let evaluating_term = term;
  while (!isValue(evaluating_term)) {
    const result = evaluate1(evaluating_term);
    if (!result.success)
      return error({
        msg: "evaluating_term is not value, but cannot eval",
        evaluating_term,
      });

    evaluating_term = result.value;
  }

  return ok(evaluating_term);
};
