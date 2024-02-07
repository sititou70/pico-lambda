import { tokenize } from "./lexer";

test("tokenize", () => {
  expect(tokenize("λx. x")).toEqual({
    success: true,
    value: [
      { kind: "token", type: "Lambda" },
      { kind: "token", type: "Identifier", value: "x" },
      { kind: "token", type: "Dot" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "Identifier", value: "x" },
      { kind: "token", type: "End" },
    ],
  });

  expect(tokenize("succ succ 0")).toEqual({
    success: true,
    value: [
      { kind: "token", type: "Succ" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "Succ" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "Zero" },
      { kind: "token", type: "End" },
    ],
  });

  expect(
    tokenize(`
x
x
  `)
  ).toEqual({
    success: true,
    value: [
      { kind: "token", type: "Identifier", value: "x" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "Identifier", value: "x" },
      { kind: "token", type: "End" },
    ],
  });

  expect(
    tokenize(`// comment 1
// comment 2
      let id = (λarg. arg) in // comment 3
      id id
    // comment 4
    `)
  ).toEqual({
    success: true,
    value: [
      { kind: "token", type: "Let" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "Identifier", value: "id" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "Equall" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "LeftParenthesis" },
      { kind: "token", type: "Lambda" },
      { kind: "token", type: "Identifier", value: "arg" },
      { kind: "token", type: "Dot" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "Identifier", value: "arg" },
      { kind: "token", type: "RightParenthesis" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "In" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "Identifier", value: "id" },
      { kind: "token", type: "Spaces" },
      { kind: "token", type: "Identifier", value: "id" },
      { kind: "token", type: "End" },
    ],
  });
});
