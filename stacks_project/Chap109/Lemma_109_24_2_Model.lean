/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Models of finite-type schemes over a DVR

A model of a finite-type scheme over the fraction field of a discrete valuation
ring is a flat finite-type morphism to `Spec R` together with an identification
of the given scheme with the generic fibre.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- A model of a finite-type scheme over the fraction field of a discrete
valuation ring, together with its identification on the generic fibre. -/
structure Model.{u} (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (V : SchemeOverField K) [FiniteType V.hom] where
  /-- The scheme underlying the model. -/
  scheme : Scheme.{u}
  /-- The structural morphism of the model over the discrete valuation ring. -/
  base : scheme ⟶ Spec (CommRingCat.of R)
  /-- The structural morphism is flat. -/
  flat : Flat base
  /-- The structural morphism is of finite type. -/
  finiteType : FiniteType base
  /-- The generic fibre is identified with the given scheme over `K`. -/
  genericFiberIso : V ≅ Over.mk
    (pullback.snd base (Spec.map (CommRingCat.ofHom (algebraMap R K))))

universe u

namespace Model

/-- Construct a model from a flat finite-type morphism to `Spec R` and a
generic-fibre identification. -/
def of {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : SchemeOverField K} [FiniteType V.hom]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (h_flat : Flat f) (h_finiteType : FiniteType f)
    (genericFiberIso : V ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    Model R K V :=
  { scheme := X
    base := f
    flat := h_flat
    finiteType := h_finiteType
    genericFiberIso := genericFiberIso }

/-- A model of `V` is a flat finite-type morphism to `Spec R` whose generic
fibre is identified with `V`. -/
theorem spec {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : SchemeOverField K} [FiniteType V.hom] (M : Model R K V) :
    Flat M.base ∧ FiniteType M.base := sorry

/-- A morphism of models is a morphism over the discrete valuation ring that
induces the identity on the generic fibre under the chosen identifications. -/
def IsMorphism {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : SchemeOverField K} [FiniteType V.hom]
    (source target : Model R K V)
    (f : Over.mk source.base ⟶ Over.mk target.base) : Prop :=
  source.genericFiberIso.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f =
    target.genericFiberIso.hom

/-- The model-morphism predicate is exactly compatibility with the chosen
generic-fibre identifications. -/
theorem isMorphism_iff {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : SchemeOverField K} [FiniteType V.hom]
    {source target : Model R K V}
    {f : Over.mk source.base ⟶ Over.mk target.base} :
    IsMorphism source target f ↔
      source.genericFiberIso.hom ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f =
        target.genericFiberIso.hom := sorry

/-- The identity over a model is a morphism of models. -/
theorem isMorphism_id {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : SchemeOverField K} [FiniteType V.hom] (model : Model R K V) :
    IsMorphism model model (𝟙 (Over.mk model.base)) := sorry

namespace IsMorphism

/-- The composite of two morphisms of models is a morphism of models. -/
theorem comp {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : SchemeOverField K} [FiniteType V.hom]
    {source middle target : Model R K V}
    {f : Over.mk source.base ⟶ Over.mk middle.base}
    {g : Over.mk middle.base ⟶ Over.mk target.base}
    (hf : IsMorphism source middle f) (hg : IsMorphism middle target g) :
    IsMorphism source target (f ≫ g) := sorry

end IsMorphism

end Model

end AlgebraicGeometry.Scheme.Hom
