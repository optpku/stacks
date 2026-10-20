/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Flat
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The scheme-theoretic image of a closed immersion of finite-type schemes over the
fraction field of a discrete valuation ring is a flat finite-type model of the source
inside a flat finite-type model of the target. -/
theorem image_isModel_of_isClosedImmersion
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (V₁ V₂ : SchemeOverField K) [FiniteType V₁.hom] [FiniteType V₂.hom]
    (i : V₁ ⟶ V₂) [IsClosedImmersion i.left]
    {X₂ : Scheme.{u}} (p₂ : X₂ ⟶ Spec (CommRingCat.of R))
    [Flat p₂] [FiniteType p₂]
    (e₂ : V₂ ≅ Over.mk
      (pullback.snd p₂ (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    let η : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R K))
    let j : V₁.left ⟶ X₂ := i.left ≫ e₂.hom.left ≫ pullback.fst p₂ η
    let p₁ : j.image ⟶ Spec (CommRingCat.of R) := j.imageι ≫ p₂
    ∃ e₁ : V₁ ≅ Over.mk (pullback.snd p₁ η),
      Flat p₁ ∧ FiniteType p₁ := sorry

end AlgebraicGeometry.Scheme.Hom
