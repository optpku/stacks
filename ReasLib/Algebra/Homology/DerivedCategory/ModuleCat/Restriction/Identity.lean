/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Algebra.Homology.Functor

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace CategoryTheory.ModuleCat.DerivedRestriction

variable {R : Type u} [CommRing R]

/-- Derived restriction along an endomorphism equal to the identity is canonically
isomorphic to the identity functor. -/
def idIsoOfEq (σ : R →+* R) (hσ : σ = RingHom.id R) :
    derivedRestrictionOfScalars.{u, v} σ ≅ 𝟭 (DerivedCategory (ModuleCat.{max u v} R)) :=
  Localization.liftNatIso
    (DerivedCategory.Q : CochainComplex (ModuleCat.{max u v} R) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (up ℤ))
    ((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q (derivedRestrictionOfScalars σ) (𝟭 _)
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId' σ hσ) (up ℤ))
        DerivedCategory.Q ≪≫ Functor.leftUnitor DerivedCategory.Q)

/-- Derived restriction along the identity ring homomorphism is the identity functor. -/
def idIso : derivedRestrictionOfScalars.{u, v} (RingHom.id R) ≅
    𝟭 (DerivedCategory (ModuleCat.{max u v} R)) :=
  idIsoOfEq (RingHom.id R) rfl

/-- The identity comparison on a localized complex is induced by the
underived identity restriction comparison. -/
theorem idIsoOfEq_hom_app_Q (σ : R →+* R) (hσ : σ = RingHom.id R)
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (idIsoOfEq σ hσ).hom.app (DerivedCategory.Q.obj K) =
      (ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.hom.app K ≫
        (Functor.isoWhiskerRight
          (NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId' σ hσ) (up ℤ))
            DerivedCategory.Q ≪≫ Functor.leftUnitor DerivedCategory.Q).hom.app K := sorry

end CategoryTheory.ModuleCat.DerivedRestriction
