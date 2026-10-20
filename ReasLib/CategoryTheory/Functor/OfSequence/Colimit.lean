module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Colimit maps from sequential diagrams

This file packages the common construction of a morphism out of the colimit of
`Functor.ofSequence`.  It keeps the one-step compatibility condition as the
input, matching the API of `NatTrans.ofSequence`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

namespace ofSequence

namespace constCocone

/-- The cocone naturality condition for a compatible family on a sequential diagram. -/
@[stacks 0193 "successor naturality for a sequential cocone"]
theorem naturality
    {X : C} {B : ℕ → C} (u : ∀ n : ℕ, B n ⟶ B (n + 1))
    (φ : ∀ n : ℕ, B n ⟶ X) (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n)
    (n : ℕ) :
    (Functor.ofSequence u).map (homOfLE (Nat.le_succ n)) ≫ φ (n + 1) =
      φ n ≫ ((Functor.const ℕ).obj X).map (homOfLE (Nat.le_succ n)) := sorry

end constCocone

/-- The cocone over `Functor.ofSequence u` induced by compatible maps `φ n : B n ⟶ X`. -/
@[stacks 0193 "cocone from compatible sequential maps"]
noncomputable def constCocone
    {X : C} {B : ℕ → C} (u : ∀ n : ℕ, B n ⟶ B (n + 1))
    (φ : ∀ n : ℕ, B n ⟶ X) (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n) :
    Cocone (Functor.ofSequence u) :=
  Cocone.mk X
    (NatTrans.ofSequence φ (constCocone.naturality u φ hcompat))

/-- The universal map from the colimit of a sequential diagram induced by compatible stage maps. -/
@[stacks 0193 "map from a sequential colimit"]
noncomputable def colimitDesc
    {X : C} {B : ℕ → C} (u : ∀ n : ℕ, B n ⟶ B (n + 1))
    (φ : ∀ n : ℕ, B n ⟶ X) (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n)
    [HasColimit (Functor.ofSequence u)] :
    colimit (Functor.ofSequence u) ⟶ X :=
  colimit.desc (Functor.ofSequence u) (constCocone u φ hcompat)

namespace colimitDesc

/-- The sequential colimit map restricts to `φ n` on the `n`-th colimit inclusion. -/
@[reassoc, stacks 0193 "sequential colimit map on inclusions"]
theorem ι
    {X : C} {B : ℕ → C} (u : ∀ n : ℕ, B n ⟶ B (n + 1))
    (φ : ∀ n : ℕ, B n ⟶ X) (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n)
    [HasColimit (Functor.ofSequence u)] (n : ℕ) :
    colimit.ι (Functor.ofSequence u) n ≫ colimitDesc u φ hcompat = φ n := sorry

/-- Maps out of sequential colimits are natural for maps of sequential diagrams and targets. -/
@[stacks 0193 "naturality of sequential colimit maps"]
theorem naturality
    {X Y : C} {B D : ℕ → C}
    (u : ∀ n : ℕ, B n ⟶ B (n + 1)) (v : ∀ n : ℕ, D n ⟶ D (n + 1))
    (φ : ∀ n : ℕ, B n ⟶ X) (ψ : ∀ n : ℕ, D n ⟶ Y)
    (hφ : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n)
    (hψ : ∀ n : ℕ, v n ≫ ψ (n + 1) = ψ n)
    (τ : Functor.ofSequence u ⟶ Functor.ofSequence v) (f : X ⟶ Y)
    (hτ : ∀ n : ℕ, τ.app n ≫ ψ n = φ n ≫ f)
    [HasColimitsOfShape ℕ C] :
    colim.map τ ≫ colimitDesc v ψ hψ = colimitDesc u φ hφ ≫ f := sorry

end colimitDesc

end ofSequence

end CategoryTheory.Functor
