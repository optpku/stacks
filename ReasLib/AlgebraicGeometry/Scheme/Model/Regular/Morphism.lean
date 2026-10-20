/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism between regular models is a morphism over the discrete valuation ring that
induces the identity on the curve under the chosen generic-fibre identifications. -/
def IsModelMorphism {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (source target : RegularModel R K C)
    (f : Over.mk source.base ⟶ Over.mk target.base) : Prop :=
  source.genericFiberIso.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f =
    target.genericFiberIso.hom

/-- The model-morphism predicate is exactly compatibility with the chosen generic-fibre
identifications. -/
theorem isModelMorphism_iff {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C}
    {f : Over.mk source.base ⟶ Over.mk target.base} :
    IsModelMorphism source target f ↔
      source.genericFiberIso.hom ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f =
        target.genericFiberIso.hom := Iff.rfl

/-- The identity over a regular model is a model morphism. -/
theorem isModelMorphism_id {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (model : RegularModel R K C) :
    IsModelMorphism model model (𝟙 (Over.mk model.base)) := sorry

namespace IsModelMorphism

/-- The composite of two model morphisms is a model morphism. -/
theorem comp {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source middle target : RegularModel R K C}
    {f : Over.mk source.base ⟶ Over.mk middle.base}
    {g : Over.mk middle.base ⟶ Over.mk target.base}
    (hf : IsModelMorphism source middle f) (hg : IsModelMorphism middle target g) :
    IsModelMorphism source target (f ≫ g) := sorry

end IsModelMorphism

end AlgebraicGeometry.Scheme.Hom
