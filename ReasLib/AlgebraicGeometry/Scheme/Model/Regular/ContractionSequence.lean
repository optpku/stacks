/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Contraction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite composable sequence of contractions of exceptional curves of the first kind
between regular models. -/
inductive ContractionSequence {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom] :
    RegularModel R K C → RegularModel R K C → Type (u + 2) where
  /-- The empty contraction sequence on a regular model. -/
  | nil (model : RegularModel R K C) : ContractionSequence model model
  /-- Prepend one contraction of an exceptional curve to a finite contraction sequence. -/
  | cons {source middle target : RegularModel R K C} :
      ContractionStep source middle → ContractionSequence middle target →
        ContractionSequence source target

namespace ContractionSequence

/-- The morphism over the base represented by a finite contraction sequence. -/
noncomputable def toOver {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} :
    ContractionSequence source target → (Over.mk source.base ⟶ Over.mk target.base)
  | .nil _ => 𝟙 _
  | .cons step tail => step.hom ≫ tail.toOver

/-- Regard one contraction step as a one-step contraction sequence. -/
def single {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    ContractionSequence source target :=
  .cons step (.nil target)

/-- Concatenate two finite contraction sequences. -/
def append {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source middle target : RegularModel R K C} :
    ContractionSequence source middle → ContractionSequence middle target →
      ContractionSequence source target
  | .nil _, tail => tail
  | .cons step rest, tail => .cons step (rest.append tail)

/-- The composite of the empty contraction sequence is the identity. -/
theorem toOver_nil {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (model : RegularModel R K C) :
    (ContractionSequence.nil model).toOver = 𝟙 (Over.mk model.base) := rfl

/-- The composite of a cons sequence is the first contraction followed by the tail composite. -/
theorem toOver_cons {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source middle target : RegularModel R K C} (step : ContractionStep source middle)
    (tail : ContractionSequence middle target) :
    (ContractionSequence.cons step tail).toOver = step.hom ≫ tail.toOver := rfl

/-- The composite of an appended contraction sequence is the composite of its two parts. -/
theorem toOver_append {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source middle target : RegularModel R K C}
    (head : ContractionSequence source middle) (tail : ContractionSequence middle target) :
    (head.append tail).toOver = head.toOver ≫ tail.toOver := sorry

/-- The composite represented by a contraction sequence is a morphism of regular models. -/
theorem isModelMorphism {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (sequence : ContractionSequence source target) :
    IsModelMorphism source target sequence.toOver := sorry

end ContractionSequence

/-- A morphism factors into contractions when it is the composite of a finite sequence of
contractions of exceptional curves of the first kind followed by a marked isomorphism. -/
def IsContractionSequence {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (source target : RegularModel R K C)
    (f : Over.mk source.base ⟶ Over.mk target.base) : Prop :=
  ∃ (middle : RegularModel R K C) (sequence : ContractionSequence source middle)
    (e : Over.mk middle.base ≅ Over.mk target.base),
    IsModelMorphism middle target e.hom ∧ sequence.toOver ≫ e.hom = f

/-- A morphism factors into contractions exactly when it is a finite contraction composite
followed by an isomorphism preserving the generic-fibre identification. -/
theorem isContractionSequence_iff {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C}
    {f : Over.mk source.base ⟶ Over.mk target.base} :
    IsContractionSequence source target f ↔
      ∃ (middle : RegularModel R K C) (sequence : ContractionSequence source middle)
        (e : Over.mk middle.base ≅ Over.mk target.base),
        IsModelMorphism middle target e.hom ∧ sequence.toOver ≫ e.hom = f := Iff.rfl

namespace IsContractionSequence

/-- An isomorphism preserving the generic-fibre identification factors with zero contractions. -/
theorem of_iso {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C}
    (e : Over.mk source.base ≅ Over.mk target.base)
    (he : IsModelMorphism source target e.hom) :
    IsContractionSequence source target e.hom := by
  exact ⟨source, ContractionSequence.nil source, e, he, Category.id_comp e.hom⟩

/-- A morphism represented by a contraction sequence is a morphism of regular models. -/
theorem isModelMorphism {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C}
    {f : Over.mk source.base ⟶ Over.mk target.base}
    (hf : IsContractionSequence source target f) :
    IsModelMorphism source target f := sorry

end IsContractionSequence

end AlgebraicGeometry.Scheme.Hom
