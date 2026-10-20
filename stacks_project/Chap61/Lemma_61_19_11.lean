module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.ReductionComparison

/-!
# Lemma 61.19.11

The source-facing statement is recorded by typed checks of the reusable
pro-étale reduction comparison declarations.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

/- Lemma 61.19.11
For every scheme, Noetherian coefficient ring, ideal, derived pro-étale module,
integer lower bound, and positive exponent, the hypotheses and conclusion of
assertion (1) are preserved by reduction modulo the ideal power. -/
@[stacks 09B2] #check (AlgebraicGeometry.Scheme.proEtReduction_mem_essImage :
  ∀ {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    (I : Ideal Λ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I)))]
    [((ProEt.topology X).W (A := ModuleCat.{u + 1} (Λ ⧸ I))).IsMonoidal]
    [MonoidalPreadditive (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ I)))]
    [∀ (K L : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ I))) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (Λ ⧸ I)))) (ComplexShape.up ℤ)]
    [h_derivedTensor :
      @DerivedTensor.Right.Has (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (Λ ⧸ I))) _ _ _ _ _ _]
    [(AlgebraicGeometry.Scheme.proEtModuleExtendScalars
      (Ideal.Quotient.mk I) X).Additive]
    [(Functor.Homotopy.toDerived
      (AlgebraicGeometry.Scheme.proEtModuleExtendScalars
        (Ideal.Quotient.mk I) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]
    [HasSheafify X.smallEtaleTopology
      (ModuleCat.{u + 1} (Λ ⧸ I))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Λ ⧸ I)))]
    [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I),
      (etaleToProEt X).op.HasLeftKanExtension F]
    [(etaleToProEtPullback X
      (ModuleCat.{u + 1} (Λ ⧸ I))).Additive]
    [PreservesFiniteLimits (etaleToProEtPullback X
      (ModuleCat.{u + 1} (Λ ⧸ I)))]
    [PreservesFiniteColimits (etaleToProEtPullback X
      (ModuleCat.{u + 1} (Λ ⧸ I)))]
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} Λ))) (a : ℤ)
    (h_ess :
      (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I))).mapDerivedCategory.essImage
        ((AlgebraicGeometry.Scheme.proEtDerivedExtendScalars
          (Ideal.Quotient.mk I) X).obj K))
    (h_tor : DerivedTensor.HasTorAmplitudeGE
      ((AlgebraicGeometry.Scheme.proEtDerivedExtendScalars
        (Ideal.Quotient.mk I) X).obj K) a)
    (n : ℕ+)
    [HasSheafify X.smallEtaleTopology
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasSheafify (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [HasDerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [((ProEt.topology X).W (A := ModuleCat.{u + 1}
      (Λ ⧸ I ^ (n : ℕ)))).IsMonoidal]
    [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)),
      (etaleToProEt X).op.HasLeftKanExtension F]
    [(etaleToProEtPullback X
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).Additive]
    [PreservesFiniteLimits (etaleToProEtPullback X
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [PreservesFiniteColimits (etaleToProEtPullback X
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [(AlgebraicGeometry.Scheme.proEtModuleExtendScalars
      (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
      (AlgebraicGeometry.Scheme.proEtModuleExtendScalars
        (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))],
    (etaleToProEtPullback X
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).mapDerivedCategory.essImage
      (AlgebraicGeometry.Scheme.proEtReduction I n K))

#check (AlgebraicGeometry.Scheme.proEtReduction_hasTorAmplitudeGE :
  ∀ {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    (I : Ideal Λ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I)))]
    [((ProEt.topology X).W (A := ModuleCat.{u + 1} (Λ ⧸ I))).IsMonoidal]
    [MonoidalPreadditive (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ I)))]
    [∀ (K L : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ I))) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (Λ ⧸ I)))) (ComplexShape.up ℤ)]
    [h_derivedTensor :
      @DerivedTensor.Right.Has (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (Λ ⧸ I))) _ _ _ _ _ _]
    [(AlgebraicGeometry.Scheme.proEtModuleExtendScalars
      (Ideal.Quotient.mk I) X).Additive]
    [(Functor.Homotopy.toDerived
      (AlgebraicGeometry.Scheme.proEtModuleExtendScalars
        (Ideal.Quotient.mk I) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} Λ))) (a : ℤ)
    (h_tor : DerivedTensor.HasTorAmplitudeGE
      ((AlgebraicGeometry.Scheme.proEtDerivedExtendScalars
        (Ideal.Quotient.mk I) X).obj K) a)
    (n : ℕ+)
    [HasSheafify (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [((ProEt.topology X).W (A := ModuleCat.{u + 1}
      (Λ ⧸ I ^ (n : ℕ)))).IsMonoidal]
    [(AlgebraicGeometry.Scheme.proEtModuleExtendScalars
      (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
      (AlgebraicGeometry.Scheme.proEtModuleExtendScalars
        (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]
    [MonoidalPreadditive (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ (K L : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))) (ComplexShape.up ℤ)]
    [h_derivedTensor_n :
      @DerivedTensor.Right.Has (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))) _ _ _ _ _ _],
    DerivedTensor.HasTorAmplitudeGE
      (AlgebraicGeometry.Scheme.proEtReduction I n K) a)

end
