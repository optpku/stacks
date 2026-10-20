/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Comparison
public import ReasLib.CategoryTheory.Filtration.Complex.Realization
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Targets.Abutment
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Targets.PageOne
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite filtered right-derived realizations

This file is a reusable leaf of the finite filtered right-derived spectral-sequence API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- Lemma 13.26.14 (`015W`): a chosen right-derived spectral-sequence realization constructed
from an explicit strict filtered-injective resolution. -/
@[stacks 015W "left-exact filtered right-derived spectral-sequence realization"]
structure Realization (T : A ⥤ₗ B) [EnoughInjectives A]
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) where
  /-- The strict filtered-injective resolution used by the realization. -/
  resolution : Resolution K
  /-- Cohomology comparison between the finite filtered model and the pointwise derived values. -/
  comparison : Model.Comparison T resolution
  /-- The associated spectral sequence of the degreewise image of the resolution. -/
  associated : FilteredComplex.AssociatedSpectralSequence (model T resolution)

namespace Realization

/-- The concrete filtered model underlying a finite right-derived realization. -/
@[stacks 015W "filtered model of a finite right-derived realization"]
noncomputable abbrev filtered {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    FilteredComplex B :=
  model T S.resolution

/-- The cohomological spectral sequence of a finite right-derived realization. -/
@[stacks 015W "spectral sequence of a finite right-derived realization"]
noncomputable abbrev sequence {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    CohomologicalSpectralSequence B 0 :=
  S.associated.sequence

/-- The concrete association between a finite right-derived model and its spectral sequence. -/
@[stacks 015W "association of a finite right-derived realization"]
noncomputable abbrev association {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    FilteredComplex.Association S.filtered S.sequence :=
  S.associated.association

/-- The first page of a finite realization is the derived cohomology of the original graded
pieces.  The comparison is the canonical association comparison followed by the selected model
comparison. -/
@[stacks 015W "first page of a finite filtered right-derived spectral sequence"]
noncomputable abbrev pageOneIso {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K)
    (p q : ℤ) :
    (S.sequence.page 1).X (p, q) ≅ PageOne.obj T K p q :=
  S.association.pageOneIso p q ≪≫ S.comparison.gradedPieceIso p (p + q)

/-- The forward first-page comparison is the association comparison followed by the selected
graded-piece model comparison. -/
@[simp, stacks 015W "first-page comparison for a finite filtered right-derived realization"]
theorem pageOneIso_hom {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K)
    (p q : ℤ) :
    (S.pageOneIso p q).hom =
      (S.association.pageOneIso p q).hom ≫
        (S.comparison.gradedPieceIso p (p + q)).hom := sorry

/-- The inverse first-page comparison first returns to model graded-piece homology and then to
the first page of the associated spectral sequence. -/
@[simp, stacks 015W "inverse first-page comparison for a finite filtered right-derived realization"]
theorem pageOneIso_inv {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K)
    (p q : ℤ) :
    (S.pageOneIso p q).inv =
      (S.comparison.gradedPieceIso p (p + q)).inv ≫
        (S.association.pageOneIso p q).inv := sorry

/-- The cohomology of a finite filtered model is the derived value of the original underlying
complex. -/
@[stacks 015W "abutment of a finite filtered right-derived spectral sequence"]
noncomputable abbrev targetIso {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K)
    (n : ℤ) :
    S.filtered.underlying.homology n ≅ Abutment.obj T K n :=
  S.comparison.underlyingIso n

/-- A finite right-derived realization supplies the canonical existential association
predicate. -/
@[stacks 015W "association of a finite right-derived spectral sequence"]
theorem isAssociated {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    FilteredComplex.IsAssociated S.filtered S.sequence := sorry

/-- The spectral sequence of a finite right-derived realization is bounded. -/
@[stacks 015W "boundedness of a finite filtered right-derived spectral sequence"]
theorem isBounded {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    S.sequence.IsBounded := sorry

/-- A finite right-derived realization induces finite filtrations on the cohomology of its
filtered model. -/
@[stacks 015W "finite cohomology filtration of a filtered right-derived spectral sequence"]
theorem finite {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- A finite right-derived realization converges to the cohomology of its filtered model. -/
@[stacks 015W "convergence of a finite filtered right-derived spectral sequence"]
theorem converges {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence := sorry

end Realization

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
