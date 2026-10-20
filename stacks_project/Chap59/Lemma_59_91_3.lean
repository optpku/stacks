/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProperHenselian

open CategoryTheory Opposite
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 59.91.3: if `A` is a henselian local ring and `f : X ⟶ Spec A` is proper,
then for the closed-point fibre `X₀ = X ×_{Spec A} Spec(A / m)` and the
closed immersion `i` of `X₀` into `X`, restriction identifies
`Γ(X_étale, F)` with `Γ(X₀_étale, i_small⁻¹ F)` for every sheaf of sets `F`
on `X_étale`. -/
@[stacks 0A3S] #check
  (AlgebraicGeometry.Scheme.Hom.etaleGlobalSectionsBijectiveOfProperHenselianLocal :
    {A : Type u} → [CommRing A] → [HenselianLocalRing A] →
      {X : Scheme.{u}} → (f : X ⟶ Spec (CommRingCat.of A)) → [IsProper f] →
      let φ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
      let i := pullback.fst f φ
      ∀ [HasWeakSheafify X.smallEtaleTopology (Type u)]
        [HasWeakSheafify (pullback f φ).smallEtaleTopology (Type u)]
        [∀ P : X.Etaleᵒᵖ ⥤ Type u,
          (smallEtalePullback i).op.HasLeftKanExtension P]
        (F : Sheaf X.smallEtaleTopology (Type u)),
        Function.Bijective (etaleGlobalSectionsPullback i F))
