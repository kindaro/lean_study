import Automation
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
  intros, unfold identity, unfold compose,
  dsimp {md := transparency.instances},
  crush,
end

theorem has_right_identity (α β: Type): ∀ (r: α ~ β), r ∘ identity ≡ r :=
begin
  intros, unfold identity, unfold compose,
  dsimp {md := transparency.instances},
  crush,
end

theorem has_identity (α β: Type): ∀ (r: α ~ β), (identity ∘ r ≡ r) ∧ (r ∘ identity ≡ r) :=
begin
  intros, unfold identity, unfold compose,
  dsimp {md := transparency.instances},
  crush,
end

theorem exists_identity (α β: Type): ∀ (r: α ~ β), ∃ (ε: ∀ (type: Type), type ~ type), (ε β ∘ r ≡ r) ∧ (r ∘ ε α ≡ r) :=
begin
  intros, unfold compose,
  dsimp {md := transparency.instances},
  existsi (λ τ x y, x = y), crush,
end

theorem compose_is_associative (α β γ δ: Type)
  : ∀ (r₁: α ~ β) (r₂: β ~ γ) (r₃: γ ~ δ)
  , (r₃ ∘ r₂) ∘ r₁ ≡ r₃ ∘ (r₂ ∘ r₁) :=
begin
  intros, unfold compose,
  dsimp {md := transparency.instances},
  crush,
end