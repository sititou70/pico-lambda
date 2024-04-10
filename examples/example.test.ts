import fs from "fs";
import { parse } from "../parser/parser";
import { evaluate } from "../evaluator/evaluator";
import { print } from "../printer/printer";

test.each([
  ["arithmetics.lambda", "729"],
  ["fact.lambda", "120"],
  ["poly-fixed.lambda", "λx. (x)"],
])("example: %s", (file, result) => {
  const input = fs.readFileSync(`examples/${file}`).toString();

  const parse_result = parse(input);
  expect(parse_result.success).toBe(true);
  if (!parse_result.success) return;

  const evaluate_result = evaluate(parse_result.value);
  expect(evaluate_result.success).toBe(true);
  if (!evaluate_result.success) return;

  expect(print(evaluate_result.value)).toBe(result);
});
