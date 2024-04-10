import { AST, ASTVariable, getVariableId } from "../parser/types";
import { Result, error, ok } from "../utils/Result";
import {
  TypeConstraint,
  Type,
  getFreshTypeVariable,
  ComposedTypeAssigning,
  isSameType,
  TypeVariable,
  TypeAssigning,
} from "./types";

export const inferTypeAndConatraints = (
  context: Map<string, Type>,
  term: AST
): Result<{ type: Type; constraints: TypeConstraint[] }> => {
  switch (term.type) {
    case "Variable": {
      // CT-Var
      const type = context.get(getVariableId(term));
      if (type === undefined)
        return error({ msg: "unknown variable", term, context });
      return ok({ type, constraints: [] });
    }
    case "Lambda": {
      // CT-Abs
      const argument_type = getFreshTypeVariable();
      const new_context = new Map(context);
      new_context.set(getVariableId(term.argument), argument_type);

      const result = inferTypeAndConatraints(new_context, term.body);
      if (!result.success) return result;

      return ok({
        type: {
          kind: "type",
          type: "Function",
          argument: argument_type,
          return: result.value.type,
        },
        constraints: result.value.constraints,
      });
    }
    case "Apply": {
      // CT-App
      const result1 = inferTypeAndConatraints(context, term.operator);
      if (!result1.success) return result1;

      const result2 = inferTypeAndConatraints(context, term.operand);
      if (!result2.success) return result2;

      const type = getFreshTypeVariable();

      return ok({
        type,
        constraints: [
          ...result1.value.constraints,
          ...result2.value.constraints,
          {
            lhs: result1.value.type,
            rhs: {
              kind: "type",
              type: "Function",
              argument: result2.value.type,
              return: type,
            },
          },
        ],
      });
    }
    case "Zero": {
      // CT-Zero
      return ok({
        type: { kind: "type", type: "Nat" },
        constraints: [],
      });
    }
    case "Succ": {
      // CT-Succ
      const result = inferTypeAndConatraints(context, term.body);
      if (!result.success) return result;

      return ok({
        type: { kind: "type", type: "Nat" },
        constraints: [
          ...result.value.constraints,
          { lhs: result.value.type, rhs: { kind: "type", type: "Nat" } },
        ],
      });
    }
    case "Let": {
      // CT-Let
      const result1 = inferTypeAndConatraints(context, term.value);
      if (!result1.success) return result1;

      const type = getFreshTypeVariable();
      const new_context = new Map(context);
      new_context.set(getVariableId(term.variable), type);
      const result2 = inferTypeAndConatraints(new_context, term.body);
      if (!result2.success) return result2;

      return ok({
        type: result2.value.type,
        constraints: [
          ...result1.value.constraints,
          ...result2.value.constraints,
          {
            lhs: result1.value.type,
            rhs: type,
          },
        ],
      });
    }
  }
};

const typeAssign = (assigning: TypeAssigning, type: Type): Type => {
  switch (type.type) {
    case "Function": {
      return {
        ...type,
        argument: typeAssign(assigning, type.argument),
        return: typeAssign(assigning, type.return),
      };
    }
    case "Nat": {
      return type;
    }
    case "Variable": {
      const maps_to = assigning.get(type.name);
      if (maps_to === undefined) return type;

      return maps_to;
    }
  }
};

const constraintsAssign = (
  assigning: TypeAssigning,
  constraints: TypeConstraint[]
): TypeConstraint[] =>
  constraints.map(
    (constraint): TypeConstraint => ({
      lhs: typeAssign(assigning, constraint.lhs),
      rhs: typeAssign(assigning, constraint.rhs),
    })
  );

const appearsIn = (variable: TypeVariable, type: Type): boolean => {
  switch (type.type) {
    case "Function": {
      if (appearsIn(variable, type.argument)) return true;
      if (appearsIn(variable, type.return)) return true;
      return false;
    }
    case "Nat": {
      return false;
    }
    case "Variable": {
      return isSameType(variable, type);
    }
  }
};

export const unify = (
  constraints: TypeConstraint[]
): Result<ComposedTypeAssigning> => {
  if (constraints.length === 0) return ok([]);

  const reduced_constraints = constraints.concat();
  const { lhs, rhs } = reduced_constraints.pop() as Exclude<
    (typeof reduced_constraints)[number],
    undefined
  >;

  if (isSameType(lhs, rhs)) return unify(reduced_constraints);

  if (lhs.type === "Variable" && !appearsIn(lhs, rhs)) {
    const assigning: TypeAssigning = new Map([[lhs.name, rhs]]);
    const unify_result = unify(
      constraintsAssign(assigning, reduced_constraints)
    );
    if (!unify_result.success) return unify_result;

    return ok([...unify_result.value, assigning]);
  }

  if (rhs.type === "Variable" && !appearsIn(rhs, lhs)) {
    const assigning: TypeAssigning = new Map([[rhs.name, lhs]]);
    const unify_result = unify(
      constraintsAssign(assigning, reduced_constraints)
    );
    if (!unify_result.success) return unify_result;

    return ok([...unify_result.value, assigning]);
  }

  if (lhs.type === "Function" && rhs.type === "Function") {
    return unify([
      ...constraints,
      { lhs: lhs.argument, rhs: rhs.argument },
      { lhs: lhs.return, rhs: rhs.return },
    ]);
  }

  return error({ msg: "unification failed", constraints });
};

const composedTypeAssign = (
  composed_assigning: ComposedTypeAssigning,
  type: Type
): Type =>
  composed_assigning
    .reverse()
    .reduce((type, assigning) => typeAssign(assigning, type), type);

export const inferType = (term: AST): Result<Type> => {
  const infer_result = inferTypeAndConatraints(new Map(), term);
  if (!infer_result.success)
    return error({
      msg: "inferType: inferTypeAndConatraints failed",
      error: infer_result,
    });

  const { type, constraints } = infer_result.value;

  const unification_result = unify(constraints);
  if (!unification_result.success)
    return error({
      msg: "inferType: unification failed",
      error: unification_result,
    });

  const composed_assigning = unification_result.value;
  return ok(composedTypeAssign(composed_assigning, type));
};
