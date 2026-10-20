/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.AlgebraicGeometry.Scheme.ArtinApproximation.FiniteTypeFactorization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.GradedAlgebra
public import ReasLib.RingTheory.Algebra.TensorProduct.PolynomialResolution
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Cokernel.ArtinRees
public import ReasLib.RingTheory.MvPolynomial.RelationParameter.TensorProduct

@[expose] public section

open CategoryTheory Limits IsLocalRing

universe u

namespace AlgebraicGeometry.ArtinApproximation

open Scheme.Modules

/-- A local map from the stalk of a finite-type Noetherian scheme to the completed base stalk
factors through a pointed finite-type refinement such that every other compatible factorization
has the same closed-fiber conormal algebra after transport along an isomorphism over the source
scheme. -/
theorem exists_conormalAlgebraIso
    {S T Y : Scheme.{u}} (pY : Y ⟶ T) (q : T ⟶ S)
    [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [Scheme.Hom.FiniteType pY] [Scheme.Hom.FiniteType q]
    (s : S) (t : T) (ht : q t = s)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    [IsLocalHom σ]
    (hσ_over : σ.comp (ht ▸ (q.stalkMap t).hom) =
      algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))) :
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
                Scheme.ConormalAlgebra (qσ.fiberι c)) := sorry

end AlgebraicGeometry.ArtinApproximation
