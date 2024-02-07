import { Type } from "../checker/types";
import { AST, isASTType, isSameVariable } from "../parser/types";
import { Result, error, ok } from "../utils/Result";

const parseNumber = (term: AST): Result<number> => {
  let current_term = term;
  let count = 0;
  while (true) {
    if (isASTType(current_term, "Zero")) return ok(count);

    if (!isASTType(current_term, "Succ")) return error();

    current_term = current_term.body;
    count++;
  }
};

export const print = (term: AST): string => {
  switch (term.type) {
    case "Variable": {
      return term.name;
    }
    case "Lambda": {
      return `λ${print(term.argument)}. (${print(term.body)})`;
    }
    case "Apply": {
      return `(${print(term.operator)} ${print(term.operand)})`;
    }
    case "Zero": {
      return "0";
    }
    case "Succ": {
      const result = parseNumber(term);
      if (result.success) return result.value.toString();

      return `(succ ${print(term.body)})`;
    }
    case "Let": {
      return `let ${print(term.variable)} = (${print(term.value)}) in (${print(term.body)})`;
    }
  }
};

export const printType = (type: Type): string => {
  switch (type.type) {
    case "Function": {
      return `${printType(type.argument)} → ${printType(type.return)}`;
    }
    case "Nat": {
      return "Nat";
    }
    case "Variable": {
      return type.name;
    }
  }
};
