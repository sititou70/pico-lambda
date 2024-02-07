import { parse } from "../parser/parser";
import { print } from "./printer";

test.each([
  ["var", "var"],
  ["λx. (x)", "λx. (x)"],
  ["(x y)", "(x y)"],
  ["0", "0"],
  ["succ 0", "1"],
  ["succ x", "(succ x)"],
  ["let Id = λx. (x) in Id", "let Id = (λx. (x)) in (Id)"],
])("print: %s", (input, result) => {
  const parse_result = parse(input);
  expect(parse_result.success).toBe(true);
  if (!parse_result.success) return;

  expect(print(parse_result.value)).toBe(result);
});
