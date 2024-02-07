export type Result<V, E = unknown> =
  | { success: true; value: V }
  | { success: false; error?: E };

export const ok = <V, E>(value: V): Result<V, E> => ({ success: true, value });
export const error = <V, E>(error?: E): Result<V, E> => ({
  success: false,
  error,
});
