import { Cast } from "../utils/Cast";

export type ASTVariable = {
  kind: "ast";
  type: "Variable";
  name: string;
  variant: number; // A value to represent a fresh variable
};
export type ASTLambda = {
  kind: "ast";
  type: "Lambda";
  argument: ASTVariable;
  body: AST;
};
export type ASTApply = {
  kind: "ast";
  type: "Apply";
  operator: AST;
  operand: AST;
};
export type ASTZero = {
  kind: "ast";
  type: "Zero";
};
export type ASTSucc = {
  kind: "ast";
  type: "Succ";
  body: AST;
};
export type ASTLet = {
  kind: "ast";
  type: "Let";
  variable: ASTVariable;
  value: AST;
  body: AST;
};

export type AST =
  | ASTVariable
  | ASTLambda
  | ASTApply
  | ASTZero
  | ASTSucc
  | ASTLet;

export const isAST = (ast: unknown): ast is AST => {
  if (typeof ast !== "object") return false;
  if (ast === null) return false;
  if (!("kind" in ast)) return false;
  if (ast.kind !== "ast") return false;
  if (!("type" in ast)) return false;
  if (typeof ast.type !== "string") return false;

  return true;
};

type ASTByType<Type extends AST["type"], T = AST> = T extends unknown
  ? Type extends Cast<T, AST>["type"]
    ? T
    : never
  : never;
export const isASTType = <Type extends AST["type"]>(
  ast: unknown,
  type: Type
): ast is ASTByType<Type> => {
  if (!isAST(ast)) return false;
  if (ast.type !== type) return false;

  return true;
};

export const isSameVariable = (v1: ASTVariable, v2: ASTVariable): boolean => {
  if (v1.name !== v2.name) return false;
  if (v1.variant !== v2.variant) return false;
  return true;
};

let count = 0;
export const getFreshVariableVariant = (): number => {
  count++;
  return count;
};

export const getVariableId = (variable: ASTVariable): string =>
  `${variable.name}(${variable.variant})`;
