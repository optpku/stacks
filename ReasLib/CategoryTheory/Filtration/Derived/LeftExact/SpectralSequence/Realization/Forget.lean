/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Object
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting finite right-derived realizations

These leaves forget construction-specific finite-resolution data while retaining the generic
filtered spectral-sequence interfaces used by downstream applications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- `[stacks 015W]` Forget the chosen finite right-derived resolution while retaining the generic
filtered realization and its functorial abutment comparison. -/
@[stacks 015W "generic realization with abutment of a finite right-derived spectral sequence"]
noncomputable def Realization.toWithAbutment
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    FilteredComplex.SpectralSequence.Realization.WithAbutment
      (Abutment.functor T) K where
  toRealization :=
    { filtered := S.filtered
      sequence := S.sequence
      association := S.association
      bounded := S.isBounded
      finite := S.finite
      converges := S.converges }
  abutmentIso := S.targetIso

/-- Forgetting the abutment comparison from `toWithAbutment` gives the generic filtered
realization.  This compatibility abbreviation keeps the older interface without duplicating data. -/
@[stacks 015W "generic filtered realization of a finite right-derived spectral sequence"]
noncomputable abbrev Realization.toFilteredRealization
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    FilteredComplex.SpectralSequence.Realization (C := B) :=
  S.toWithAbutment.toRealization

/-- The generic realization underlying `toWithAbutment` is `toFilteredRealization`. -/
@[simp, stacks 015W "generic realization with abutment of a finite right-derived spectral sequence"]
theorem Realization.toWithAbutment_toRealization
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    S.toWithAbutment.toRealization = S.toFilteredRealization := sorry

/-- The abutment comparison retained by the generic conversion is the original target
comparison. -/
@[simp, stacks 015W "abutment comparison of a generic finite realization"]
theorem Realization.toWithAbutment_abutmentIso
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) (n : ℤ) :
    S.toWithAbutment.abutmentIso n = S.targetIso n := sorry

/-- The filtered model of the generic realization conversion is the original finite model. -/
@[simp, stacks 015W "filtered component of a generic finite realization"]
theorem Realization.toFilteredRealization_filtered
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    S.toFilteredRealization.filtered = S.filtered := sorry

/-- The spectral sequence of the generic realization conversion is the original sequence. -/
@[simp, stacks 015W "spectral-sequence component of a generic finite realization"]
theorem Realization.toFilteredRealization_sequence
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    S.toFilteredRealization.sequence = S.sequence := sorry

/-- The association of the generic realization conversion is the original association. -/
@[simp, stacks 015W "association component of a generic finite realization"]
theorem Realization.toFilteredRealization_association
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    S.toFilteredRealization.association = S.association := sorry

/-- The generic realization conversion retains the boundedness certificate. -/
@[simp, stacks 015W "boundedness component of a generic finite realization"]
theorem Realization.toFilteredRealization_bounded
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    S.toFilteredRealization.bounded = S.isBounded := sorry

/-- The generic realization conversion retains the finite-filtration certificate. -/
@[simp, stacks 015W "finiteness component of a generic finite realization"]
theorem Realization.toFilteredRealization_finite
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    S.toFilteredRealization.finite = S.finite := sorry

/-- The generic realization conversion retains the convergence certificate. -/
@[simp, stacks 015W "convergence component of a generic finite realization"]
theorem Realization.toFilteredRealization_converges
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    S.toFilteredRealization.converges = S.converges := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
