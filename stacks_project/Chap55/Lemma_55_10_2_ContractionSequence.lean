module

public import stacks_project.Chap55.Lemma_55_10_2_ModelMorphism
public import stacks_project.Chap55.Lemma_55_8_5_Contraction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

namespace ContractionStep

/-- The morphism over the discrete valuation ring underlying one contraction step. -/
noncomputable def toOver {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    Over.mk source.base ⟶ Over.mk target.base :=
  Over.homMk step.morphism step.over

/-- The map underlying a contraction step is a morphism of regular models. -/
theorem isModelMorphism {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    IsModelMorphism source target step.toOver := sorry

end ContractionStep

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
  | .cons step tail => step.toOver ≫ tail.toOver

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
    (ContractionSequence.nil model).toOver = 𝟙 (Over.mk model.base) := sorry

/-- The composite of a cons sequence is the first contraction followed by the tail composite. -/
theorem toOver_cons {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source middle target : RegularModel R K C} (step : ContractionStep source middle)
    (tail : ContractionSequence middle target) :
    (ContractionSequence.cons step tail).toOver = step.toOver ≫ tail.toOver := sorry

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

/-- A model morphism is a contraction sequence when it is the composite of a finite sequence
of contractions of exceptional curves of the first kind. -/
def IsContractionSequence {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (source target : RegularModel R K C)
    (f : Over.mk source.base ⟶ Over.mk target.base) : Prop :=
  ∃ sequence : ContractionSequence source target, sequence.toOver = f

/-- A morphism is represented by contractions exactly when it is the composite of a finite
contraction sequence. -/
theorem isContractionSequence_iff {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C}
    {f : Over.mk source.base ⟶ Over.mk target.base} :
    IsContractionSequence source target f ↔
      ∃ sequence : ContractionSequence source target, sequence.toOver = f := sorry

namespace IsContractionSequence

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
