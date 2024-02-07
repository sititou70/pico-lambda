import { Cast } from "../../utils/Cast";

export type TokenLambda = { kind: "token"; type: "Lambda" };
export type TokenDot = { kind: "token"; type: "Dot" };
export type TokenLet = { kind: "token"; type: "Let" };
export type TokenEquall = { kind: "token"; type: "Equall" };
export type TokenIn = { kind: "token"; type: "In" };
export type TokenZero = { kind: "token"; type: "Zero" };
export type TokenSucc = { kind: "token"; type: "Succ" };
export type TokenLeftParenthesis = { kind: "token"; type: "LeftParenthesis" };
export type TokenRightParenthesis = { kind: "token"; type: "RightParenthesis" };
export type TokenSpaces = { kind: "token"; type: "Spaces" };
export type TokenIdentifier = {
  kind: "token";
  type: "Identifier";
  value: string;
};
export type TokenEnd = {
  kind: "token";
  type: "End";
};

export type Token =
  | TokenLambda
  | TokenDot
  | TokenLet
  | TokenEquall
  | TokenIn
  | TokenZero
  | TokenSucc
  | TokenLeftParenthesis
  | TokenRightParenthesis
  | TokenSpaces
  | TokenIdentifier
  | TokenEnd;

export const isToken = (token: unknown): token is Token => {
  if (typeof token !== "object") return false;
  if (token === null) return false;
  if (!("kind" in token)) return false;
  if (token.kind !== "token") return false;
  if (!("type" in token)) return false;
  if (typeof token.type !== "string") return false;

  return true;
};

type TokenByType<Type extends Token["type"], T = Token> = T extends unknown
  ? Type extends Cast<T, Token>["type"]
    ? T
    : never
  : never;
export const isTokenType = <Type extends Token["type"]>(
  token: unknown,
  type: Type
): token is TokenByType<Type> => {
  if (!isToken(token)) return false;
  if (token.type !== type) return false;

  return true;
};
