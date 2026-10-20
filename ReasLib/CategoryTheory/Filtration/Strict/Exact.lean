module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.Strict
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact Short Complexes of Finite Filtered Objects

This file provides the reusable exactness-detection API for a short complex of filtered objects.
Associated-graded exactness first descends degreewise, then detects exactness on stages and
quotients for finite filtrations.  Two independent bridge theorems expose the strictness
criteria used by the combined result.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.ShortComplex

open FilteredObject FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (FilteredObject C)}

namespace Filtered

namespace AssociatedGraded

/-- Exactness of an associated-graded short complex can be evaluated in every degree. -/
@[stacks 05QH]
theorem exact_piece
    (hgr : (S.map associatedGradedFunctor).Exact) (p : ℤ) :
    (S.map (associatedGradedFunctor ⋙ GradedObject.eval p)).Exact := sorry

/-- For finite filtrations, associated-graded exactness implies exactness on every filtration
stage. -/
@[stacks 05QH]
theorem exact_stage
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : (S.map associatedGradedFunctor).Exact) (p : ℤ) :
    (S.map (Stage.functor p)).Exact := sorry

/-- For finite filtrations, associated-graded exactness implies exactness after quotienting by
every filtration stage. -/
@[stacks 05QH]
theorem exact_quotient
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : (S.map associatedGradedFunctor).Exact) (p : ℤ) :
    (S.map (quotientFunctor p)).Exact := sorry

/-- For finite filtrations, associated-graded exactness forces the first differential to be
strict. -/
@[stacks 05QH]
theorem strict_f
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : (S.map associatedGradedFunctor).Exact) : Strict S.f := sorry

/-- For finite filtrations, associated-graded exactness forces the second differential to be
strict. -/
@[stacks 05QH]
theorem strict_g
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : (S.map associatedGradedFunctor).Exact) : Strict S.g := sorry

/-- For finite filtrations, associated-graded exactness implies exactness of the underlying short
complex. -/
@[stacks 05QH]
theorem exact_underlying
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : (S.map associatedGradedFunctor).Exact) :
    (S.map FilteredObject.forget).Exact := sorry

end AssociatedGraded

namespace Exact

/-- Exactness on every stage together with underlying exactness forces the first differential to
be strict. -/
theorem strict_f_of_stage
    (hunder : (S.map FilteredObject.forget).Exact)
    (hstage : ∀ p : ℤ, (S.map (Stage.functor p)).Exact) : Strict S.f := sorry

/-- Exactness after every filtration quotient forces the second differential to be strict. -/
theorem strict_g_of_quotient
    (hquot : ∀ p : ℤ, (S.map (quotientFunctor p)).Exact) : Strict S.g := sorry

end Exact

end Filtered

end CategoryTheory.ShortComplex
