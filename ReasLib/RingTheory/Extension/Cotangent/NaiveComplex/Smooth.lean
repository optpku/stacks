module

public import Mathlib.RingTheory.Smooth.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ProjectiveCriterion
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness from the naive cotangent complex

This file owns the smoothness and formal-smoothness criteria expressed by degree-one Ext
vanishing for the derived naive cotangent object.

@stack 0G9D
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u v

namespace Algebra

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

local notation "NL" => naiveCotangentObject A B
local notation "single₀" =>
  DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)

/-- Remark 15.85.2 (1): an `A`-algebra `B` is smooth if and only if it is of finite
presentation and `Ext¹_B(NL{B/A}, N)` vanishes for every `B`-module `N`. -/
@[stacks 0G9D "Remark 15.85.2 (1)"]
theorem smooth_iff_finitePresentation_and_naiveCotangent_extOne_vanishes :
    Smooth A B ↔
      FinitePresentation A B ∧
        ∀ (N : ModuleCat B), ∀ e : Ext⁽(1 : ℤ)⁾(NL, (single₀).obj N), e = 0 := sorry
/- Proof strategy: rewrite smoothness as finite presentation plus formal smoothness, identify formal
smoothness with projectivity of `H⁰(NL)` and vanishing of `H⁻¹(NL)`, and apply
`DerivedCategory.TwoTerm.cohomology_projective_iff_extOne_vanishes` using the canonical
cohomological bounds on the derived naive cotangent object. -/

/-- Remark 15.85.2 (2): an `A`-algebra `B` is formally smooth if and only if
`Ext¹_B(NL{B/A}, N)` vanishes for every `B`-module `N`. -/
@[stacks 0G9D "Remark 15.85.2 (2)"]
theorem formallySmooth_iff_naiveCotangent_extOne_vanishes :
    FormallySmooth A B ↔
      ∀ (N : ModuleCat B), ∀ e : Ext⁽(1 : ℤ)⁾(NL, (single₀).obj N), e = 0 := sorry
/- Proof strategy: use the naive-cotangent characterization of formal smoothness to express the
left side as vanishing of `H⁻¹(NL)` plus projectivity of `H⁰(NL)`, then invoke the two-term
projectivity/Ext criterion with the standard support bounds for `NL`. -/

/-- The zero Ext-functor form of the smoothness criterion for the naive cotangent object. -/
@[stacks 0G9D "smoothness via the degree-one Ext functor"]
theorem smooth_iff_finitePresentation_and_naiveCotangent_extOneFunctor_isZero :
    Smooth A B ↔
      FinitePresentation A B ∧
        IsZero (CategoryTheory.DerivedCategory.Ext.addCommGrpFunctor NL (1 : ℤ)) := sorry
/- Proof strategy: rewrite the pointwise Ext-vanishing conjunct in
`smooth_iff_finitePresentation_and_naiveCotangent_extOne_vanishes` by the zero-functor
characterization `DerivedCategory.TwoTerm.cohomology_projective_iff_extOneFunctor_isZero`. -/

/-- The zero Ext-functor form of the formal-smoothness criterion for the naive cotangent
object. -/
@[stacks 0G9D "formal smoothness via the degree-one Ext functor"]
theorem formallySmooth_iff_naiveCotangent_extOneFunctor_isZero :
    FormallySmooth A B ↔
      IsZero (CategoryTheory.DerivedCategory.Ext.addCommGrpFunctor NL (1 : ℤ)) := sorry
/- Proof strategy: compose `formallySmooth_iff_naiveCotangent_extOne_vanishes` with the
pointwise-zero iff for `DerivedCategory.Ext.addCommGrpFunctor NL 1`. -/

end

end Algebra
