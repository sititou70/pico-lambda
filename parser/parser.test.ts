import { parse } from "./parser";

test("identifire", () => {
  const result = parse("x");

  expect(result.success).toBe(true);
  if (!result.success) return;

  expect(result.value).toMatchObject({
    kind: "ast",
    type: "Variable",
    name: "x",
  });
});

test("lambda", () => {
  const result = parse("λx. x");

  expect(result.success).toBe(true);
  if (!result.success) return;

  expect(result.value).toMatchObject({
    kind: "ast",
    type: "Lambda",
    argument: { kind: "ast", type: "Variable", name: "x" },
    body: { kind: "ast", type: "Variable", name: "x" },
  });
});

describe("apply", () => {
  test("x y", () => {
    const result = parse("x y");

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.value).toMatchObject({
      kind: "ast",
      type: "Apply",
      operator: { kind: "ast", type: "Variable", name: "x" },
      operand: { kind: "ast", type: "Variable", name: "y" },
    });
  });

  test("x y z", () => {
    const result = parse("x y z");

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.value).toMatchObject({
      kind: "ast",
      type: "Apply",
      operator: {
        kind: "ast",
        type: "Apply",
        operator: { kind: "ast", type: "Variable", name: "x" },
        operand: { kind: "ast", type: "Variable", name: "y" },
      },
      operand: { kind: "ast", type: "Variable", name: "z" },
    });
  });

  test("(x (y z))", () => {
    const result = parse("(x (y z))");

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.value).toMatchObject({
      kind: "ast",
      type: "Apply",
      operator: { kind: "ast", type: "Variable", name: "x" },
      operand: {
        kind: "ast",
        type: "Apply",
        operator: { kind: "ast", type: "Variable", name: "y" },
        operand: { kind: "ast", type: "Variable", name: "z" },
      },
    });
  });
});

test("zero", () => {
  const result = parse("0");

  expect(result.success).toBe(true);
  if (!result.success) return;

  expect(result.value).toMatchObject({ kind: "ast", type: "Zero" });
});

test("succ", () => {
  const result = parse("succ succ x");

  expect(result.success).toBe(true);
  if (!result.success) return;

  expect(result.value).toMatchObject({
    kind: "ast",
    type: "Succ",
    body: {
      kind: "ast",
      type: "Succ",
      body: { kind: "ast", type: "Variable", name: "x", variant: 0 },
    },
  });
});

describe("let", () => {
  test("simple", () => {
    const result = parse("let x = y in z");

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.value).toMatchObject({
      kind: "ast",
      type: "Let",
      variable: { kind: "ast", type: "Variable", name: "x" },
      value: { kind: "ast", type: "Variable", name: "y" },
      body: { kind: "ast", type: "Variable", name: "z" },
    });
  });

  test("nested", () => {
    const result = parse(`
      let x = y in
      let z = x in
      z
    `);

    expect(result.success).toBe(true);
    if (!result.success) return;

    expect(result.value).toMatchObject({
      kind: "ast",
      type: "Let",
      variable: { kind: "ast", type: "Variable", name: "x", variant: 0 },
      value: { kind: "ast", type: "Variable", name: "y", variant: 0 },
      body: {
        kind: "ast",
        type: "Let",
        variable: { kind: "ast", type: "Variable", name: "z", variant: 0 },
        value: { kind: "ast", type: "Variable", name: "x", variant: 0 },
        body: { kind: "ast", type: "Variable", name: "z", variant: 0 },
      },
    });
  });
});

test("complex 1", () => {
  // see: https://sititou70.github.io/Z%E3%82%B3%E3%83%B3%E3%83%93%E3%83%8D%E3%83%BC%E3%82%BF%E3%82%92%E6%80%9D%E3%81%84%E3%81%A4%E3%81%8D%E3%81%9F%E3%81%84/
  const result = parse(`
    let z = (
      λg. (
        λh. (
          g (λarg. (h h arg))
        )
        λh. (
          g (λarg. (h h arg))
        )
      )
    ) in
    
    z
  `);

  expect(result.success).toBe(true);
  if (!result.success) return;

  expect(result.value).toMatchObject({
    kind: "ast",
    type: "Let",
    variable: { kind: "ast", type: "Variable", name: "z" },
    value: {
      kind: "ast",
      type: "Lambda",
      argument: { kind: "ast", type: "Variable", name: "g" },
      body: {
        kind: "ast",
        type: "Apply",
        operator: {
          kind: "ast",
          type: "Lambda",
          argument: { kind: "ast", type: "Variable", name: "h" },
          body: {
            kind: "ast",
            type: "Apply",
            operator: { kind: "ast", type: "Variable", name: "g" },
            operand: {
              kind: "ast",
              type: "Lambda",
              argument: { kind: "ast", type: "Variable", name: "arg" },
              body: {
                kind: "ast",
                type: "Apply",
                operator: {
                  kind: "ast",
                  type: "Apply",
                  operator: {
                    kind: "ast",
                    type: "Variable",
                    name: "h",
                  },
                  operand: { kind: "ast", type: "Variable", name: "h" },
                },
                operand: { kind: "ast", type: "Variable", name: "arg" },
              },
            },
          },
        },
        operand: {
          kind: "ast",
          type: "Lambda",
          argument: { kind: "ast", type: "Variable", name: "h" },
          body: {
            kind: "ast",
            type: "Apply",
            operator: { kind: "ast", type: "Variable", name: "g" },
            operand: {
              kind: "ast",
              type: "Lambda",
              argument: { kind: "ast", type: "Variable", name: "arg" },
              body: {
                kind: "ast",
                type: "Apply",
                operator: {
                  kind: "ast",
                  type: "Apply",
                  operator: {
                    kind: "ast",
                    type: "Variable",
                    name: "h",
                  },
                  operand: { kind: "ast", type: "Variable", name: "h" },
                },
                operand: { kind: "ast", type: "Variable", name: "arg" },
              },
            },
          },
        },
      },
    },
  });
});
