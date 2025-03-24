import { parse } from "../parser/parser";
import { inferType, inferTypeAndConstraints } from "./checker";
import { Type, isSameType } from "./types";

test.each([
  [
    "0",
    {
      success: true,
      value: { type: { kind: "type", type: "Nat" }, constraints: [] },
    },
  ],
  [
    "succ 0",
    {
      success: true,
      value: {
        type: { kind: "type", type: "Nat" },
        constraints: [
          {
            lhs: { kind: "type", type: "Nat" },
            rhs: { kind: "type", type: "Nat" },
          },
        ],
      },
    },
  ],
  [
    "λx. x",
    {
      success: true,
      value: {
        type: {
          kind: "type",
          type: "Function",
          argument: { kind: "type", type: "Variable" },
          return: { kind: "type", type: "Variable" },
        },
        constraints: [],
      },
    },
  ],
])("inferTypeAndConstraints: %s", (input, expected_result) => {
  const parse_result = parse(input);
  expect(parse_result.success).toBe(true);
  if (!parse_result.success) return;

  const result = inferTypeAndConstraints(new Map(), parse_result.value);
  expect(result).toMatchObject(expected_result);
});

test.each([
  ["0", { success: true, value: { kind: "type", type: "Nat" } }],
  ["succ 0", { success: true, value: { kind: "type", type: "Nat" } }],
  ["succ (succ 0)", { success: true, value: { kind: "type", type: "Nat" } }],
  ["(λx. x) 0", { success: true, value: { kind: "type", type: "Nat" } }],
  [
    `
      (λx.
        λy.
          λz.
            (
              (x z)
              (y z)
            )
      )
      λz. λyz. (yz (succ z))
      λz. λa. a
      0`,
    { success: true, value: { kind: "type", type: "Nat" } },
  ],
])("inferType: %s", (input, expected_result) => {
  const parse_result = parse(input);
  expect(parse_result.success).toBe(true);
  if (!parse_result.success) return;

  const result = inferType(parse_result.value);
  expect(result).toMatchObject(expected_result);
});

test("inferType: id", () => {
  const parse_result = parse("λx. x");
  expect(parse_result.success).toBe(true);
  if (!parse_result.success) return;

  const result = inferType(parse_result.value);
  expect(result.success).toBe(true);
  if (!result.success) return;

  const type = result.value;
  expect(type.type).toBe("Function");
  if (type.type !== "Function") return;

  expect(isSameType(type.argument, type.return)).toBe(true);
});

// see: TAPL 22.3.3
test("inferType: λx. λy. λz. ((x z) (y z))", () => {
  const parse_result = parse("λx. λy. λz. ((x z) (y z))");
  expect(parse_result.success).toBe(true);
  if (!parse_result.success) return;

  const result = inferType(parse_result.value);
  expect(result.success).toBe(true);
  if (!result.success) return;

  const type = result.value;
  expect(type).toMatchObject({
    kind: "type",
    type: "Function",
    argument: {
      kind: "type",
      type: "Function",
      argument: { kind: "type", type: "Variable" },
      return: {
        kind: "type",
        type: "Function",
        argument: { kind: "type", type: "Variable" },
        return: { kind: "type", type: "Variable" },
      },
    },
    return: {
      kind: "type",
      type: "Function",
      argument: {
        kind: "type",
        type: "Function",
        argument: { kind: "type", type: "Variable" },
        return: { kind: "type", type: "Variable" },
      },
      return: {
        kind: "type",
        type: "Function",
        argument: { kind: "type", type: "Variable" },
        return: { kind: "type", type: "Variable" },
      },
    },
  });

  const Z = (type.type === "Function" &&
    type.argument &&
    type.argument.type === "Function" &&
    type.argument.argument) as Type;
  const B = (type.type === "Function" &&
    type.argument &&
    type.argument.type === "Function" &&
    type.argument.return.type === "Function" &&
    type.argument.return.argument) as Type;
  const C = (type.type === "Function" &&
    type.argument &&
    type.argument.type === "Function" &&
    type.argument.return.type === "Function" &&
    type.argument.return.return) as Type;

  expect(
    isSameType(
      Z,
      (type.type === "Function" &&
        type.return.type === "Function" &&
        type.return.argument.type === "Function" &&
        type.return.argument.argument) as Type
    )
  ).toBe(true);
  expect(
    isSameType(
      B,
      (type.type === "Function" &&
        type.return.type === "Function" &&
        type.return.argument.type === "Function" &&
        type.return.argument.return) as Type
    )
  ).toBe(true);

  expect(
    isSameType(
      Z,
      (type.type === "Function" &&
        type.return.type === "Function" &&
        type.return.return.type === "Function" &&
        type.return.return.argument) as Type
    )
  ).toBe(true);
  expect(
    isSameType(
      C,
      (type.type === "Function" &&
        type.return.type === "Function" &&
        type.return.return.type === "Function" &&
        type.return.return.return) as Type
    )
  ).toBe(true);
});
