/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.LowLength

/-!
# Lengthwise existence and extension for finite Postnikov systems

This leaf packages the two uniform properties whose failure first occurs in lengths two and
three: extension of row morphisms to chosen Postnikov systems, and existence of a Postnikov
system on every complex row. Keeping the ambient-category quantification outside these predicates
makes obstruction statements usable without repeating the full finite-system signature.
-/

@[expose] public section

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

variable (D : Type u) [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

namespace PostnikovSystem

/-- Every complex row of length `n` in `D` admits a finite Postnikov system. -/
@[stacks 0D81 "lengthwise existence of finite Postnikov systems"]
def ExistsAtLength (n : ℕ) : Prop :=
  ∀ (X : ComposableArrows D n), X.IsComplex → Nonempty (PostnikovSystem X)

namespace ExistsAtLength

/-- Apply lengthwise existence to a complex row. -/
theorem nonempty {n : ℕ} (h : ExistsAtLength D n) (X : ComposableArrows D n)
    (hX : X.IsComplex) :
    Nonempty (PostnikovSystem X) := sorry

/-- Every triangulated category has finite Postnikov systems in length zero. -/
@[stacks 0D81 "uniform length-zero Postnikov-system existence"]
theorem zero : ExistsAtLength D 0 := sorry

/-- Every triangulated category has finite Postnikov systems in length one. -/
@[stacks 0D81 "uniform length-one Postnikov-system existence"]
theorem one : ExistsAtLength D 1 := sorry

/-- Every triangulated category has finite Postnikov systems on complex rows in length two. -/
@[stacks 0D81 "uniform length-two Postnikov-system existence"]
theorem two : ExistsAtLength D 2 := sorry

end ExistsAtLength

namespace Morphism

/-- Every row morphism of length `n` extends between any chosen Postnikov systems. -/
@[stacks 0D81 "lengthwise extension of finite Postnikov-system morphisms"]
def ExtendsAtLength (n : ℕ) : Prop :=
  ∀ {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X'), Nonempty (PostnikovSystem.Morphism P P' φ)

namespace ExtendsAtLength

/-- Apply lengthwise morphism extension to chosen finite Postnikov systems. -/
theorem nonempty {n : ℕ} (h : ExtendsAtLength D n)
    {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') :
    Nonempty (PostnikovSystem.Morphism P P' φ) := sorry

/-- Row morphisms between length-zero finite Postnikov systems always extend. -/
@[stacks 0D81 "uniform length-zero Postnikov morphism extension"]
theorem zero : ExtendsAtLength D 0 := sorry

/-- Row morphisms between length-one finite Postnikov systems always extend. -/
@[stacks 0D81 "uniform length-one Postnikov morphism extension"]
theorem one : ExtendsAtLength D 1 := sorry

end ExtendsAtLength

/-- Lemma 13.41.3 (7): extension of row morphisms between length-two Postnikov systems is not a
property of all triangulated categories. -/
@[stacks 0D81 "failure of universal length-two Postnikov morphism extension"]
theorem ExtendsAtLength.not_forall_two :
    ¬ ∀ {D : Type 1} [Category.{0} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D],
      ExtendsAtLength D 2 := sorry

end Morphism

/-- Uniform extension of length-two Postnikov-system morphisms would imply uniform existence of
length-three Postnikov systems. -/
@[stacks 0D81 "length-three existence from length-two morphism extension"]
theorem ExistsAtLength.three_of_extends_two
    (h : Morphism.ExtendsAtLength D 2) :
    ExistsAtLength D 3 := sorry

/-- Lemma 13.41.3 (8): for every `n > 2`, existence of Postnikov systems on all complex rows of
length `n` is not a property of all triangulated categories. -/
@[stacks 0D81 "failure of universal finite Postnikov-system existence"]
theorem ExistsAtLength.not_forall_of_two_lt (n : ℕ) (hn : 2 < n) :
    ¬ ∀ {D : Type 1} [Category.{0} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D],
      ExistsAtLength D n := sorry

end PostnikovSystem

end CategoryTheory
