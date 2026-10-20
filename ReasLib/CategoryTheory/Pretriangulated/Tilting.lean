/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generic Tilting Objects

This leaf owns the intrinsic tilting-object predicate used by derived Morita statements.  It is
deliberately independent of a chosen enhancement, algebra model, or realization of a derived
category.  Ordinary and differential graded versions should expose thin aliases to this owner.
-/

@[expose] public section

noncomputable section

universe uR uE₁ uE₂ uC vC

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- An object is self-orthogonal when every morphism to a nontrivial integer shift of itself
vanishes.  This is the shift-theoretic condition used independently inside tilting predicates. -/
@[stacks 09S8 "self-orthogonal object in a category with shifts"]
def IsSelfOrthogonal
    {C : Type uC} [Category.{vC, uC} C] [HasZeroMorphisms C] [HasShift C ℤ]
    (P : C) : Prop :=
  ∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0

/-- The defining shifted-Hom vanishing condition for a self-orthogonal object. -/
@[stacks 09S8 "shifted-Hom criterion for self-orthogonality"]
theorem isSelfOrthogonal_iff
    {C : Type uC} [Category.{vC, uC} C] [HasZeroMorphisms C] [HasShift C ℤ]
    (P : C) :
    IsSelfOrthogonal P ↔ ∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0 := sorry

/-- Every nonzero shifted self-morphism of a self-orthogonal object is zero. -/
theorem IsSelfOrthogonal.eq_zero
    {C : Type uC} [Category.{vC, uC} C] [HasZeroMorphisms C] [HasShift C ℤ]
    {P : C} (hP : IsSelfOrthogonal P) (i : ℤ) (hi : i ≠ 0) (f : P ⟶ P⟦i⟧) :
    f = 0 := sorry

/-- Every nonzero shifted self-Hom of a self-orthogonal object is a subsingleton. -/
theorem IsSelfOrthogonal.subsingleton
    {C : Type uC} [Category.{vC, uC} C] [HasZeroMorphisms C] [HasShift C ℤ]
    {P : C} (hP : IsSelfOrthogonal P) (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (P ⟶ P⟦i⟧) := sorry

/-- A tilting object is compact, weakly generating, has no nonzero shifted self-morphisms, and has
the prescribed degree-zero endomorphism algebra.  The target algebra and the ambient category are
independent of one another, so this predicate can be reused for ordinary, DG, and enhanced
derived categories alike. -/
@[stacks 09S8 "generic tilting-object predicate"]
def IsTiltingFor {R : Type uR} [CommSemiring R]
    {E : Type uE₁} [Semiring E] [Algebra R E]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C]
    [Linear R C] [HasShift C ℤ] (P : C) : Prop :=
  IsCompactObject P ∧
    IsWeakGenerator P ∧
    IsSelfOrthogonal P ∧
    Nonempty (End P ≃ₐ[R] E)

/-- The four intrinsic conditions defining a tilting object. -/
@[stacks 09S8 "intrinsic criterion for a tilting object"]
theorem isTiltingFor_iff {R : Type uR} [CommSemiring R]
    {E : Type uE₁} [Semiring E] [Algebra R E]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C]
    [Linear R C] [HasShift C ℤ] (P : C) :
    IsTiltingFor (R := R) (E := E) P ↔
      IsCompactObject P ∧ IsWeakGenerator P ∧ IsSelfOrthogonal P ∧
        Nonempty (End P ≃ₐ[R] E) := sorry

/-- A tilting object is compact. -/
@[stacks 09S8 "compactness projection from a tilting object"]
theorem IsTiltingFor.isCompact {R : Type uR} [CommSemiring R]
    {E : Type uE₁} [Semiring E] [Algebra R E]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C]
    [Linear R C] [HasShift C ℤ] {P : C}
    (hP : IsTiltingFor (R := R) (E := E) P) : IsCompactObject P := sorry

/-- A tilting object is a weak generator. -/
@[stacks 09S8 "weak-generation projection from a tilting object"]
theorem IsTiltingFor.isWeakGenerator {R : Type uR} [CommSemiring R]
    {E : Type uE₁} [Semiring E] [Algebra R E]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C]
    [Linear R C] [HasShift C ℤ] {P : C}
    (hP : IsTiltingFor (R := R) (E := E) P) : IsWeakGenerator P := sorry

/-- A tilting object is self-orthogonal. -/
@[stacks 09S8 "self-orthogonality projection from a tilting object"]
theorem IsTiltingFor.isSelfOrthogonal {R : Type uR} [CommSemiring R]
    {E : Type uE₁} [Semiring E] [Algebra R E]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C]
    [Linear R C] [HasShift C ℤ] {P : C}
    (hP : IsTiltingFor (R := R) (E := E) P) : IsSelfOrthogonal P := sorry

/-- Every nonzero-degree self-morphism of a tilting object vanishes. -/
@[stacks 09S8 "shifted self-extension projection from a tilting object"]
theorem IsTiltingFor.selfExt_eq_zero {R : Type uR} [CommSemiring R]
    {E : Type uE₁} [Semiring E] [Algebra R E]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C]
    [Linear R C] [HasShift C ℤ] {P : C}
    (hP : IsTiltingFor (R := R) (E := E) P) (i : ℤ) (hi : i ≠ 0) (f : P ⟶ P⟦i⟧) :
    f = 0 := sorry

/-- The endomorphism algebra of a tilting object is identified with the prescribed algebra. -/
@[stacks 09S8 "endomorphism-algebra projection from a tilting object"]
theorem IsTiltingFor.nonempty_endEquiv {R : Type uR} [CommSemiring R]
    {E : Type uE₁} [Semiring E] [Algebra R E]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C]
    [Linear R C] [HasShift C ℤ] {P : C}
    (hP : IsTiltingFor (R := R) (E := E) P) : Nonempty (End P ≃ₐ[R] E) := sorry

/-- Replacing the prescribed algebra by an `R`-algebra equivalent to it does not change the
tilting predicate. -/
@[stacks 09S8 "tilting predicate invariant under algebra equivalence"]
theorem isTiltingFor_congr {R : Type uR} [CommSemiring R]
    {E₁ : Type uE₁} [Semiring E₁] [Algebra R E₁]
    {E₂ : Type uE₂} [Semiring E₂] [Algebra R E₂]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C]
    [Linear R C] [HasShift C ℤ] (P : C) (e : E₁ ≃ₐ[R] E₂) :
    IsTiltingFor (R := R) (E := E₁) P ↔ IsTiltingFor (R := R) (E := E₂) P := sorry

/-- The algebra-equivalence invariance of tilting objects can be used directly from a
`Nonempty` equivalence, without choosing a public representative. -/
@[stacks 09S8 "tilting predicate invariant under a nonempty algebra equivalence"]
theorem isTiltingFor_congr_of_nonempty {R : Type uR} [CommSemiring R]
    {E₁ : Type uE₁} [Semiring E₁] [Algebra R E₁]
    {E₂ : Type uE₂} [Semiring E₂] [Algebra R E₂]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C]
    [Linear R C] [HasShift C ℤ] (P : C)
    (e : Nonempty (E₁ ≃ₐ[R] E₂)) :
    IsTiltingFor (R := R) (E := E₁) P ↔ IsTiltingFor (R := R) (E := E₂) P := sorry

end CategoryTheory
