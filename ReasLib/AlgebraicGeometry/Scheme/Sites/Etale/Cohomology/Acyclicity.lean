/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsWithSupport
public import ReasLib.CategoryTheory.Sites.Cech.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Direct image of abelian sheaves along the small étale pullback of `f`. -/
abbrev etaleAbelianPushforward :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{w} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{w} :=
  (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{w}
    Y.smallEtaleTopology X.smallEtaleTopology

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
variable (V : Y.Etale)

/-- Positive Čech cohomology of the direct image of an injective étale sheaf vanishes on every
covering family of an étale object. -/
theorem etalePushforward_cechCohomology_isZero_of_injective
    {ι : Type w} (𝒱 : ι → Over V) [HasFiniteProducts (Over V)]
    [HasProducts.{w} AddCommGrpCat.{u}]
    (h𝒱 : (Y.smallEtaleTopology.over V).CoversTop 𝒱)
    (p : ℕ) (hp : 0 < p) :
    IsZero
      ((cechCohomologyOnSheaves Y.smallEtaleTopology 𝒱 p).obj
        ((etaleAbelianPushforward f).obj I)) := sorry

/-- Preadditive structure on small-étale abelian sheaves induced by `Abelian`. -/
instance sheafSmallEtale_preadditive (S : Scheme.{u})
    [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})] :
    Preadditive (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :=
  Abelian.toPreadditive

/-- Zero morphisms on small-étale abelian sheaves induced by the preadditive structure. -/
instance sheafSmallEtale_hasZeroMorphisms (S : Scheme.{u})
    [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})] :
    HasZeroMorphisms (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- The direct image of an injective étale sheaf is acyclic for sections over an étale object. -/
theorem etalePushforward_sections_rightDerived_isZero_of_injective
    [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [(siteAbelianSectionsFunctor Y.smallEtaleTopology V).Additive]
    (p : ℕ) (hp : 0 < p) :
    IsZero
      (((siteAbelianSectionsFunctor Y.smallEtaleTopology V).rightDerived p).obj
        ((etaleAbelianPushforward f).obj I)) := sorry

variable {Z : Scheme.{u}} (g : Y ⟶ Z)
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]

/-- The direct image of an injective étale sheaf is acyclic for a subsequent direct image. -/
theorem etalePushforward_comp_rightDerived_isZero_of_injective
    [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [(etaleAbelianPushforward g).Additive]
    (p : ℕ) (hp : 0 < p) :
    IsZero
      (((etaleAbelianPushforward g).rightDerived p).obj
        ((etaleAbelianPushforward f).obj I)) := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Etale

/-- Positive right-derived sections with support vanish on the direct image of an injective
abelian sheaf along a closed immersion. -/
theorem sectionsWithSupport_rightDerived_isZero_of_injective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [(sectionsWithSupport i).Additive]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) [Injective G]
    (p : ℕ) (hp : 0 < p) :
    IsZero (((sectionsWithSupport i).rightDerived p).obj
      ((etaleAbelianPushforward i).obj G)) := sorry

end AlgebraicGeometry.Scheme.Etale
