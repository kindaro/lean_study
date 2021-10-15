open tactic

meta def map: (expr → tactic unit) → list expr → tactic unit
  | f [] := failed
  | f (x :: xs) := f x <|> map f xs

meta def size : expr → nat
| (expr.app f a) := size f + size a
| _ := 1

meta def sort_of_identifier: expr → string
 | (expr.var nat) := "var"
 | (expr.sort level) := "sort"
 | (expr.const name list_level) := "const"
 | (expr.mvar unique pretty type) := "mvar"
 | (expr.local_const unique pretty info type) := "local_const"
 | (expr.app expr₁ expr₂) := ("apply (" ++ (sort_of_identifier expr₁ ++ " (" ++ to_string expr₁ ++ ")) to " ++ sort_of_identifier expr₂))
 | (expr.lam name info type body) := "lam"
 | (expr.pi var_name info var_type body) := "pi"
 | (expr.elet var_name type assignment body) := "elet"
 | (expr.macro macro_def list_expr) := "macro"

meta def sort_of_goal: tactic unit := target >>= λ expression, trace (sort_of_identifier expression)

meta def normalize_once: tactic unit :=
do
  context ← local_context,
  map (λ hypothesis, do cases hypothesis, return ()) context

meta def normalize := repeat normalize_once

meta def split_once: tactic unit :=
do intros, split, return ()

meta def split_all := repeat split_once

meta def triviality := repeat (assumption <|> reflexivity)

meta def existence := do
  context ← local_context,
  map (λ hypothesis, do existsi hypothesis) context

meta def is_exists: expr → tactic bool := λ target, do
  match target with
    | expr.app (expr.const `Exists _) _ := return tt
    | expr.app recurse _ := is_exists recurse
    | _ := return ff
    end

meta def is_target_exists: tactic bool := do
  target ← target,
  is_exists target

meta def slice_and_dice := do
  target ← target,
  is_exists_target ← is_exists target,
  match is_exists_target with
    | tt := existence
    | ff := split >> intros >> return ()
  end

meta def crush_once: tactic unit := do
  intros, normalize, try (interactive.simp none none tt [ ] [ ] (interactive.loc.ns [none])), repeat (do slice_and_dice >> intros >> return ()), triviality

meta def repeat_safely (operate: tactic unit): tactic unit := do
  current_target ← target,
  operate,
  next_target ← target,
  (unify current_target next_target >> return ()) <|> operate

meta def crush := repeat crush_once