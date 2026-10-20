/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Reduction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Comparison of pro-étale reductions with the étale site

Reduction modulo a power of an ideal preserves essential-image membership and
lower Tor-amplitude bounds for derived module sheaves on the pro-étale site.
-/

@[expose] public section

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

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
variable (I : Ideal Λ)
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I)))]
variable [((ProEt.topology X).W (A := ModuleCat.{u + 1} (Λ ⧸ I))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I)))]
variable [∀ (K L : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I))) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I))))
    (ComplexShape.up ℤ)]
variable [h_derivedTensor :
  @DerivedTensor.Right.Has (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I)))
    _ _ _ _ _ _]
variable [(proEtModuleExtendScalars (Ideal.Quotient.mk I) X).Additive]
variable [(Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk I) X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]

/-- For a Noetherian coefficient ring, reduction of a derived pro-étale module
whose first quotient is étale in origin remains in that essential image at every
positive ideal power. -/
@[stacks 09B2]
theorem proEtReduction_mem_essImage
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I)))]
    [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I),
      (etaleToProEt X).op.HasLeftKanExtension F]
    [(etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I))).Additive]
    [PreservesFiniteLimits (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I)))]
    [PreservesFiniteColimits (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I)))]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) (a : ℤ)
    (h_ess :
      (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I))).mapDerivedCategory.essImage
        ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (h_tor : DerivedTensor.HasTorAmplitudeGE
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K) a) (n : ℕ+)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [((ProEt.topology X).W (A := ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).IsMonoidal]
    [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)),
      (etaleToProEt X).op.HasLeftKanExtension F]
    [(etaleToProEtPullback X
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).Additive]
    [PreservesFiniteLimits
      (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [PreservesFiniteColimits
      (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))] :
    (etaleToProEtPullback X
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).mapDerivedCategory.essImage
      (proEtReduction I n K) :=
  sorry

/-- A lower Tor-amplitude bound for a derived pro-étale module is preserved by
reduction modulo every positive power of an ideal. -/
@[stacks 09B2]
theorem proEtReduction_hasTorAmplitudeGE
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) (a : ℤ)
    (h_tor : DerivedTensor.HasTorAmplitudeGE
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K) a) (n : ℕ+)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [((ProEt.topology X).W (A := ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).IsMonoidal]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]
    [MonoidalPreadditive
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ (K L : CochainComplex
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))))
        (ComplexShape.up ℤ)]
    [h_derivedTensor_n :
      @DerivedTensor.Right.Has
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))
        _ _ _ _ _ _] :
    DerivedTensor.HasTorAmplitudeGE (proEtReduction I n K) a :=
  sorry

end AlgebraicGeometry.Scheme

end

end
