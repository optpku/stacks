module

public import ReasLib.CategoryTheory.ComposableArrows.Complex
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Construction
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Low-Length Finite Postnikov Systems

This leaf owns the unconditional length-zero and length-one constructions,
the complex-controlled length-two construction, and the corresponding
low-length lifting properties for morphisms of finite Postnikov systems.
-/

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

namespace PostnikovSystem

/-- Stacks 0D81, Lemma 13.41.3: a length-zero row has a Postnikov system. -/
@[stacks 0D81]
theorem nonempty_zero (X : ComposableArrows D 0) : Nonempty (PostnikovSystem X) := sorry

/-- Stacks 0D81, Lemma 13.41.3: a length-one row has a Postnikov system. -/
@[stacks 0D81]
theorem nonempty_one (X : ComposableArrows D 1) : Nonempty (PostnikovSystem X) := sorry

/-- Stacks 0D81, Lemma 13.41.3: a complex length-two row has a Postnikov system. -/
@[stacks 0D81]
theorem nonempty_two (X : ComposableArrows D 2) (hX : X.IsComplex) :
    Nonempty (PostnikovSystem X) := sorry

/-- A length-three complex has a Postnikov system when every length-two row morphism extends
to a morphism of Postnikov systems. -/
@[stacks 0D81]
theorem nonempty_three_of_morphism_extension_two
    (hExt : ∀ {X X' : ComposableArrows D 2} (P : PostnikovSystem X) (P' : PostnikovSystem X')
      (φ : X ⟶ X'), Nonempty (PostnikovSystem.Morphism P P' φ))
    {X : ComposableArrows D 3} (hX : X.IsComplex) :
    Nonempty (PostnikovSystem X) := sorry

end PostnikovSystem

namespace PostnikovSystem.Morphism

/-- Stacks 0D81, Lemma 13.41.3: every length-zero row morphism extends to a morphism of
Postnikov systems. -/
@[stacks 0D81]
theorem nonempty_zero {X X' : ComposableArrows D 0} (P : PostnikovSystem X)
    (P' : PostnikovSystem X') (φ : X ⟶ X') :
    Nonempty (PostnikovSystem.Morphism P P' φ) := sorry

/-- Stacks 0D81, Lemma 13.41.3: the lift of a length-zero row morphism is unique. -/
@[stacks 0D81]
theorem subsingleton_zero {X X' : ComposableArrows D 0} (P : PostnikovSystem X)
    (P' : PostnikovSystem X') (φ : X ⟶ X') :
    Subsingleton (PostnikovSystem.Morphism P P' φ) := sorry

/-- Stacks 0D81, Lemma 13.41.3: every length-one row morphism extends to a morphism of
Postnikov systems. -/
@[stacks 0D81]
theorem nonempty_one {X X' : ComposableArrows D 1} (P : PostnikovSystem X)
    (P' : PostnikovSystem X') (φ : X ⟶ X') :
    Nonempty (PostnikovSystem.Morphism P P' φ) := sorry

end PostnikovSystem.Morphism

end

end CategoryTheory
