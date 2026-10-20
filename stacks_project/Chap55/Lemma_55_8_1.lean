/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Model

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.8.1: if `V₁ ⟶ V₂` is a closed immersion of algebraic schemes over the
fraction field `K` of a discrete valuation ring `R`, then its scheme-theoretic image in a
model `X₂` of `V₂` is a model of `V₁`. -/
@[stacks 0C2S] #check
(AlgebraicGeometry.Scheme.Hom.image_isModel_of_isClosedImmersion :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (V₁ V₂ : SchemeOverField K) [FiniteType V₁.hom] [FiniteType V₂.hom]
      (i : V₁ ⟶ V₂) [IsClosedImmersion i.left]
      {X₂ : Scheme.{u}} (p₂ : X₂ ⟶ Spec (CommRingCat.of R))
      [Flat p₂] [FiniteType p₂]
      (e₂ : V₂ ≅ Over.mk
        (pullback.snd p₂ (Spec.map (CommRingCat.ofHom (algebraMap R K))))) ,
      let η : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
        Spec.map (CommRingCat.ofHom (algebraMap R K))
      let j : V₁.left ⟶ X₂ := i.left ≫ e₂.hom.left ≫ pullback.fst p₂ η
      let p₁ : j.image ⟶ Spec (CommRingCat.of R) := j.imageι ≫ p₂
      ∃ e₁ : V₁ ≅ Over.mk (pullback.snd p₁ η),
        Flat p₁ ∧ FiniteType p₁)

end AlgebraicGeometry.Scheme.Hom
