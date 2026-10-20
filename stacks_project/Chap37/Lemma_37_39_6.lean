/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.ArtinApproximation.ConormalAlgebra
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits IsLocalRing

universe u

namespace AlgebraicGeometry.ArtinApproximation

open Scheme.Modules

/- Lemma 37.39.6: a local map from the stalk of a finite-type Noetherian scheme to the
completed base stalk factors through a pointed finite-type refinement so that every other
compatible factorization has the same closed-fiber conormal algebra, after transport along
an isomorphism over `Y`. -/
@[stacks 0CAY] #check
  (AlgebraicGeometry.ArtinApproximation.exists_conormalAlgebraIso :
    ∀ {S T Y : Scheme.{u}} (pY : Y ⟶ T) (q : T ⟶ S)
        [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
        [Scheme.Hom.FiniteType pY] [Scheme.Hom.FiniteType q]
        (s : S) (t : T) (ht : q t = s)
        (σ : T.presheaf.stalk t →+*
          AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
        [IsLocalHom σ]
        (hσ_over : σ.comp (ht ▸ (q.stalkMap t).hom) =
          algebraMap (S.presheaf.stalk s)
            (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))),
      ∃ (T' : Scheme.{u}) (t' : T') (g : T' ⟶ T)
          (hfinite : Scheme.Hom.FiniteType g) (hgt : g t' = t)
          (τ : T'.presheaf.stalk t' →+*
            AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
          (hτ : τ.comp (hgt ▸ (g.stalkMap t').hom) = σ),
        ∀ (σ' : T.presheaf.stalk t →+*
            AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
            [IsLocalHom σ'],
          σ'.comp (ht ▸ (q.stalkMap t).hom) =
              algebraMap (S.presheaf.stalk s)
                (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                  (S.presheaf.stalk s)) →
            (∃ τ' : T'.presheaf.stalk t' →+*
                AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                  (S.presheaf.stalk s),
              τ'.comp (hgt ▸ (g.stalkMap t').hom) = σ') →
            let Rhat :=
              AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)
            let jσ : Spec (CommRingCat.of Rhat) ⟶ T :=
              Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t
            let jσ' : Spec (CommRingCat.of Rhat) ⟶ T :=
              Spec.map (CommRingCat.ofHom σ') ≫ T.fromSpecStalk t
            let Yσ : Scheme.{u} := pullback pY jσ
            let Yσ' : Scheme.{u} := pullback pY jσ'
            let qσ : Yσ ⟶ Spec (CommRingCat.of Rhat) := pullback.snd pY jσ
            let qσ' : Yσ' ⟶ Spec (CommRingCat.of Rhat) := pullback.snd pY jσ'
            let c : Spec (CommRingCat.of Rhat) := closedPoint Rhat
            ∃ e :
                Over.mk (qσ.fiberι c ≫ pullback.fst pY jσ) ≅
                  Over.mk (qσ'.fiberι c ≫ pullback.fst pY jσ'),
              Nonempty
                (GradedAlgebra.pullback e.hom.left
                    (Scheme.ConormalAlgebra (qσ'.fiberι c)) ≅
                  Scheme.ConormalAlgebra (qσ.fiberι c)))

end AlgebraicGeometry.ArtinApproximation
