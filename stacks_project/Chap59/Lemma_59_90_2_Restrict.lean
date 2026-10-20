/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.BoundedBelow.Restriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open CategoryTheory.Functor.RightDerived.Bounded
open CategoryTheory.ExactFunctor.Derived.Plus

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Etale

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    ((siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}))]

/- Restriction of bounded-below étale hypercohomology along a scheme morphism. -/
#check (AlgebraicGeometry.Scheme.Etale.derivedEtaleCohomologyRestrict :
    ∀ {Z X : Scheme.{u}} (p : Z ⟶ X)
    [(etaleAbelianSheafPullback p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etaleAbelianSheafPullback p ⋙
        siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (q : ℤ),
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).obj
      ((functor
          (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X))).obj E) ⟶
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).obj
        ((functor
            (siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z))).obj
          ((etaleDerivedInverseImage p).obj E)))

end AlgebraicGeometry.Scheme.Etale

end

end
