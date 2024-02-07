import { Result, error, ok } from "../utils/Result";
import { Token, isTokenType } from "./lexer/types";
import {
  AST,
  ASTApply,
  ASTLambda,
  ASTLet,
  ASTSucc,
  ASTVariable,
  ASTZero,
  isAST,
  isASTType,
} from "./types";

type Syntax<NonterminalSymbol extends string> = {
  initial_symbol: NonterminalSymbol;
  rules: {
    symbol: NonterminalSymbol;
    expression: (NonterminalSymbol | Token["type"])[];
    callback: (symbols: (AST | Token)[]) => Result<AST>;
  }[];
};

export const SYNTAX: Syntax<"**start**" | "Term"> = {
  initial_symbol: "**start**",
  rules: [
    {
      symbol: "**start**",
      expression: ["Term", "End"],
      callback: (symbols): Result<AST> => {
        const term = symbols[0];
        if (!isAST(term)) return error();

        return ok(term);
      },
    },

    {
      symbol: "Term",
      expression: ["Identifier"],
      callback: (symbols): Result<ASTVariable> => {
        const identifier = symbols[0];
        if (!isTokenType(identifier, "Identifier")) return error();

        return ok({
          kind: "ast",
          type: "Variable",
          name: identifier.value,
          variant: 0,
        });
      },
    },
    {
      symbol: "Term",
      expression: ["Lambda", "Identifier", "Dot", "Spaces", "Term"],
      callback: (symbols): Result<ASTLambda> => {
        const identifier = symbols[1];
        const body = symbols[4];
        if (!isTokenType(identifier, "Identifier")) return error();
        if (!isAST(body)) return error();

        return ok({
          kind: "ast",
          type: "Lambda",
          argument: {
            kind: "ast",
            type: "Variable",
            name: identifier.value,
            variant: 0,
          },
          body,
        });
      },
    },
    {
      symbol: "Term",
      expression: ["Term", "Spaces", "Term"],
      callback: (symbols): Result<ASTApply> => {
        const operator = symbols[0];
        const operand = symbols[2];
        if (!isAST(operator)) return error();
        if (!isAST(operand)) return error();

        return ok({ kind: "ast", type: "Apply", operator, operand });
      },
    },
    {
      symbol: "Term",
      expression: ["Zero"],
      callback: (symbols): Result<ASTZero> => {
        const zero = symbols[0];
        if (!isTokenType(zero, "Zero")) return error();

        return ok({ kind: "ast", type: "Zero" });
      },
    },
    {
      symbol: "Term",
      expression: ["Succ", "Spaces", "Term"],
      callback: (symbols): Result<ASTSucc> => {
        const succ = symbols[0];
        const body = symbols[2];
        if (!isTokenType(succ, "Succ")) return error();
        if (!isAST(body)) return error();

        return ok({ kind: "ast", type: "Succ", body });
      },
    },
    {
      symbol: "Term",
      expression: [
        "Let",
        "Spaces",
        "Identifier",
        "Spaces",
        "Equall",
        "Spaces",
        "Term",
        "Spaces",
        "In",
        "Spaces",
        "Term",
      ],
      callback: (symbols): Result<ASTLet> => {
        const identifier = symbols[2];
        const value = symbols[6];
        const body = symbols[10];
        if (!isTokenType(identifier, "Identifier")) return error();
        if (!isAST(value)) return error();
        if (!isAST(body)) return error();

        return ok({
          kind: "ast",
          type: "Let",
          variable: {
            kind: "ast",
            type: "Variable",
            name: identifier.value,
            variant: 0,
          },
          value,
          body,
        });
      },
    },

    // Parenthesis
    {
      symbol: "Term",
      expression: ["LeftParenthesis", "Term", "RightParenthesis"],
      callback: (symbols) => {
        const term = symbols[1];
        if (!isAST(term)) return error();

        return ok(term);
      },
    },
    {
      symbol: "Term",
      expression: [
        "LeftParenthesis",
        "Spaces",
        "Term",
        "Spaces",
        "RightParenthesis",
      ],
      callback: (symbols) => {
        const term = symbols[2];
        if (!isAST(term)) return error();

        return ok(term);
      },
    },
    {
      symbol: "Term",
      expression: ["LeftParenthesis", "Term", "Spaces", "RightParenthesis"],
      callback: (symbols) => {
        const term = symbols[1];
        if (!isAST(term)) return error();

        return ok(term);
      },
    },
    {
      symbol: "Term",
      expression: ["LeftParenthesis", "Spaces", "Term", "RightParenthesis"],
      callback: (symbols) => {
        const term = symbols[2];
        if (!isAST(term)) return error();

        return ok(term);
      },
    },
  ],
};
