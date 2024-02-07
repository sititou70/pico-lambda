// type
export type TypeFunction = {
  kind: "type";
  type: "Function";
  argument: Type;
  return: Type;
};
export type TypeNat = {
  kind: "type";
  type: "Nat";
};
export type TypeVariable = {
  kind: "type";
  type: "Variable";
  name: string;
};

export type Type = TypeFunction | TypeNat | TypeVariable;

let count = 0;
export const getFreshTypeVariable = (): TypeVariable => {
  count++;
  return { kind: "type", type: "Variable", name: `T_${count}` };
};

export const isSameType = (t1: Type, t2: Type): boolean => {
  if (t1.kind !== t2.kind) return false;
  if (t1.type !== t2.type) return false;

  switch (t1.type) {
    case "Function": {
      if (!isSameType(t1.argument, (t2 as typeof t1).argument)) return false;
      if (!isSameType(t1.return, (t2 as typeof t1).return)) return false;
      return true;
    }
    case "Nat": {
      return true;
    }
    case "Variable": {
      if (t1.name !== (t2 as typeof t1).name) return false;
      return true;
    }
  }
};

// constraint
export type TypeConstraint = {
  lhs: Type;
  rhs: Type;
};

// assigning
export type TypeAssigning = Map<string, Type>;

// composed assigning
// [A, B, C] = A ∘ B ∘ C
export type ComposedTypeAssigning = TypeAssigning[];
