open tactic

def ℙ := Prop
class Same (φ: Type) := (same: φ → φ → ℙ)
notation x `≡` y := Same.same x y
instance Same_arrow (α β: Type) [Same β]: Same (α → β) := Same.mk (λ f₁ f₂, ∀ x, f₁ x ≡ f₂ x)
instance Same_proposition: Same ℙ := Same.mk (λ p q, p ↔ q)

notation α `~` β := α → β → ℙ
def identity {α}: α ~ α := λ x y, x = y
def compose {α β γ}
  : (α ~ β) → (β ~ γ) → (α ~ γ)
  := λ r₁ r₂, λ x z, ∃ y, (r₁ x y ∧ r₂ y z)
local notation r₂ `∘` r₁ := compose r₁ r₂

theorem has_left_identity (α β: Type): ∀ (r: α ~ β), identity ∘ r ≡ r :=
begin
  intros,unfold identity, unfold compose,
  dsimp {md := transparency.instances},
  intros x y, split,
      intro H, cases H with x' proof, cases proof, subst proof_right, apply proof_left,
      intro H, existsi y, split,
        assumption,
        reflexivity,
end

theorem has_right_identity (α β: Type): ∀ (r: α ~ β), r ∘ identity ≡ r :=
begin
  intros,unfold identity, unfold compose,
  dsimp {md := transparency.instances},
  intros, split,
    intro H, cases H with x' proof, cases proof, subst proof_left, apply proof_right,
    intro H, existsi x, split,
      reflexivity,
      assumption,
end

meta def map: (expr → tactic unit) → list expr → tactic unit
  | f [] := failed
  | f (x :: xs) := f x <|> map f xs

meta def normalize_once: tactic unit :=
do
  context ← local_context,
  map (λ hypothesis, do cases hypothesis, return ()) context

meta def normalize := repeat normalize_once

meta def split_once: tactic unit :=
do intros, split, return ()

meta def split_all := repeat split_once

meta def triviality := repeat assumption

meta def existence := do
  context ← local_context,
  map (λ hypothesis, do existsi hypothesis) context

theorem compose_is_associative (α β γ δ: Type)
  : ∀ (r₁: α ~ β) (r₂: β ~ γ) (r₃: γ ~ δ)
  , (r₃ ∘ r₂) ∘ r₁ ≡ r₃ ∘ (r₂ ∘ r₁) :=
begin
  intros, unfold compose,
  dsimp {md := transparency.instances},
  intros x₁ x₄, split,
    { intros, normalize, existence, split, existence, split, triviality },
    { intros, normalize, existence, split, assumption, existence, split, triviality },
end
