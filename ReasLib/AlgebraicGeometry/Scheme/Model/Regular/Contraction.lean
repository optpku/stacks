/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Contraction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MinimalModel

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- A contraction step between regular models, including its exceptional curve and
compatibility with the structural morphisms and generic-fibre identifications. -/
structure ContractionStep.{u} {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (source target : RegularModel R K C) where
  /-- The morphism from the source model to the target model over the base. -/
  hom : Over.mk source.base ⟶ Over.mk target.base
  /-- The exceptional ideal sheaf on the source model. -/
  exceptionalIdeal : source.scheme.IdealSheafData
  /-- The closed point contracted by the morphism. -/
  center : closedPoints target.scheme
  /-- The ideal defines an exceptional curve of the first kind, the morphism contracts it
  to the center, and the generic-fibre identifications are preserved. -/
  conditions : ∃ h_exceptional : IsExceptionalCurveFirstKind exceptionalIdeal,
    @IsContraction source.scheme target.scheme source.isNoetherian
      exceptionalIdeal h_exceptional hom.left center ∧
      (source.genericFiberIso.hom.left ≫
          pullback.fst source.base (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
          hom.left =
        target.genericFiberIso.hom.left ≫
          pullback.fst target.base (Spec.map (CommRingCat.ofHom (algebraMap R K))))

universe u

namespace ContractionStep

/-- The exceptional ideal of a contraction step defines a curve of the first kind. -/
theorem exceptional {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    IsExceptionalCurveFirstKind step.exceptionalIdeal := by
  obtain ⟨h_exceptional, h_contraction, h_genericFiber⟩ := step.conditions
  exact h_exceptional

/-- A contraction step contracts its exceptional curve to its chosen center. -/
theorem contraction {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    @IsContraction source.scheme target.scheme source.isNoetherian
      step.exceptionalIdeal step.exceptional step.hom.left step.center := by
  obtain ⟨h_exceptional, h_contraction, h_genericFiber⟩ := step.conditions
  exact h_contraction

/-- A contraction step commutes with the first projections of the identified generic fibres. -/
theorem genericFiber_fst {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    source.genericFiberIso.hom.left ≫
        pullback.fst source.base (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
        step.hom.left =
      target.genericFiberIso.hom.left ≫
        pullback.fst target.base (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨h_exceptional, h_contraction, h_genericFiber⟩ := step.conditions
  exact h_genericFiber

/-- A contraction step preserves the chosen identifications of the generic fibres. -/
theorem genericFiber {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    source.genericFiberIso.hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map step.hom =
      target.genericFiberIso.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun arrow => source.genericFiberIso.hom.left ≫ arrow)
        (pullback.lift_fst _ _ _)).trans step.genericFiber_fst)
  · exact (Over.w (source.genericFiberIso.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map step.hom)).trans
      (Over.w target.genericFiberIso.hom).symm

/-- The underlying morphism of schemes of a contraction step. -/
noncomputable def morphism {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    source.scheme ⟶ target.scheme :=
  step.hom.left

/-- The underlying morphism of a contraction step commutes with the structural morphisms. -/
theorem over {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    step.morphism ≫ target.base = source.base :=
  Over.w step.hom

/-- A contraction step induces the identity under the chosen generic-fibre identifications. -/
theorem genericFiber_identity {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    source.genericFiberIso.hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
          (Over.homMk step.morphism step.over : Over.mk source.base ⟶ Over.mk target.base) =
      target.genericFiberIso.hom := by
  simpa only [morphism, Over.homMk_eta] using step.genericFiber

/-- Construct a contraction step from its morphism, exceptional-curve data, and compatibility law. -/
noncomputable def ofData {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (morphism : source.scheme ⟶ target.scheme)
    (exceptionalIdeal : source.scheme.IdealSheafData)
    (h_exceptional : IsExceptionalCurveFirstKind exceptionalIdeal)
    (center : closedPoints target.scheme)
    (h_contraction : @IsContraction source.scheme target.scheme source.isNoetherian
      exceptionalIdeal h_exceptional morphism center)
    (h_over : morphism ≫ target.base = source.base)
    (h_genericFiber :
      source.genericFiberIso.hom ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
            (Over.homMk morphism h_over : Over.mk source.base ⟶ Over.mk target.base) =
        target.genericFiberIso.hom) : ContractionStep source target :=
  { hom := Over.homMk morphism h_over
    exceptionalIdeal := exceptionalIdeal
    center := center
    conditions := ⟨h_exceptional, h_contraction, by
      have h_fst := congrArg
        (fun arrow : C ⟶ Over.mk
            (pullback.snd target.base (Spec.map (CommRingCat.ofHom (algebraMap R K)))) =>
          arrow.left ≫
            pullback.fst target.base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        h_genericFiber
      exact ((Category.assoc _ _ _).trans
        (congrArg (fun arrow => source.genericFiberIso.hom.left ≫ arrow)
          (pullback.lift_fst _ _ _))).symm.trans h_fst⟩ }

/-- A contraction step is a morphism over the base and induces the identity on the
identified generic fibre. -/
theorem spec {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (step : ContractionStep source target) :
    step.morphism ≫ target.base = source.base ∧
      source.genericFiberIso.hom ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
            (Over.homMk step.morphism step.over : Over.mk source.base ⟶ Over.mk target.base) =
        target.genericFiberIso.hom :=
  ⟨step.over, step.genericFiber_identity⟩

end ContractionStep

/-- Every regular proper model of a smooth projective curve with only constant global
functions admits a finite sequence of contractions of exceptional curves of the first kind
ending in a minimal model. -/
theorem exists_contractionSequence
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (M : RegularModel R K C) :
    ∃ m : ℕ, ∃ models : Fin (m + 1) → RegularModel R K C,
      models (Fin.last m) = M ∧
        ∃ contractions : ∀ i : Fin m, ContractionStep (models i.succ) (models i.castSucc),
          IsMinimalModel (models 0).base := sorry

end AlgebraicGeometry.Scheme.Hom
