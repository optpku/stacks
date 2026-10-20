/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek.Basic
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap103.Lemma_103_14_2_Sites

/-!
# Morphisms of topoi induced by the lisse-étale and flat-fppf inclusions

Each inclusion is continuous and cocontinuous, so it determines a morphism of
topoi whose inverse image is restriction. The set-valued and abelian lower
shrieks are the corresponding sheaf pullbacks.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The morphism of topoi
`g : Sh(X_lisse,étale) ⟶ Sh(X_étale)` induced by the lisse-étale inclusion. -/
def lisseEtaleToposHom (X : GroupoidsOver S) [AlgebraicStack X] :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      X.etaleTopology (lisseEtaleTopology X) :=
  (lisseEtaleInclusion X).morphismOfTopoiInOfCocontinuous
    (lisseEtaleTopology X) X.etaleTopology

/-- The underlying inverse image of `lisseEtaleToposHom` is the sheafified
cocontinuous pullback. -/
theorem lisseEtaleToposHom_inverseImage (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleToposHom X).inverseImage =
      (lisseEtaleInclusion X).sheafPullbackCocontinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology :=
  sorry

/-- The underlying direct image of `lisseEtaleToposHom` is the cocontinuous
sheaf pushforward. -/
theorem lisseEtaleToposHom_pushforward (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleToposHom X).pushforward =
      (lisseEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology :=
  sorry

/-- The comparison from cocontinuous pullback to restriction along the
lisse-étale inclusion. -/
def lisseEtaleRestrictionComparison (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInclusion X).sheafPullbackCocontinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⟶
      (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology :=
  CocontinuousPullback.comparison.{u} (lisseEtaleInclusion X)
    (lisseEtaleTopology X) X.etaleTopology

/-- Restriction along the lisse-étale inclusion identifies the cocontinuous
inverse image with continuous pushforward. -/
instance lisseEtaleRestrictionComparison.instIsIso
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsIso (lisseEtaleRestrictionComparison X) :=
  sorry

/-- Restriction along the lisse-étale inclusion is precomposition with the
opposite inclusion on underlying presheaves. -/
theorem lisseEtaleInclusion_restriction_spec (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
          (lisseEtaleTopology X) X.etaleTopology ⋙
        sheafToPresheaf (lisseEtaleTopology X) (Type u) =
      sheafToPresheaf X.etaleTopology (Type u) ⋙
        (whiskeringLeft _ _ (Type u)).obj (lisseEtaleInclusion X).op :=
  sorry

/-- Set-valued lower shriek `g_!^{Sh}` along the lisse-étale inclusion. -/
abbrev lisseEtaleLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    Sheaf (lisseEtaleTopology X) (Type u) ⥤ Sheaf X.etaleTopology (Type u) :=
  (lisseEtaleInclusion X).sheafPullback (Type u)
    (lisseEtaleTopology X) X.etaleTopology

/-- Set-valued lower shriek is left adjoint to restriction. -/
abbrev lisseEtaleLowerShriek.adjunction (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleLowerShriek X ⊣
      (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology :=
  (lisseEtaleInclusion X).sheafAdjunctionContinuous (Type u)
    (lisseEtaleTopology X) X.etaleTopology

/-- Restriction along the lisse-étale inclusion is left adjoint to cocontinuous
direct image. -/
abbrev lisseEtaleSheafAdjunctionCocontinuous (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⊣
      (lisseEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology :=
  (lisseEtaleInclusion X).sheafAdjunctionCocontinuous (Type u)
    (lisseEtaleTopology X) X.etaleTopology

/-- The unit `id ⟶ g^{-1} g_!^{Sh}` is an isomorphism on sheaves of sets. -/
theorem lisseEtaleLowerShriek_unit_app_isIso (X : GroupoidsOver S)
    [AlgebraicStack X] (F : Sheaf (lisseEtaleTopology X) (Type u)) :
    IsIso ((lisseEtaleLowerShriek.adjunction X).unit.app F) :=
  sorry

/-- The counit `g^{-1} g_* ⟶ id` is an isomorphism on sheaves of sets. -/
theorem lisseEtaleSheafAdjunctionCocontinuous_counit_app_isIso
    (X : GroupoidsOver S) [AlgebraicStack X]
    (F : Sheaf (lisseEtaleTopology X) (Type u)) :
    IsIso ((lisseEtaleSheafAdjunctionCocontinuous X).counit.app F) :=
  sorry

/-- Abelian lower shriek `g_!` along the lisse-étale inclusion. -/
abbrev lisseEtaleAbelianLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u} ⥤
      Sheaf X.etaleTopology AddCommGrpCat.{u} :=
  (lisseEtaleInclusion X).sheafPullback AddCommGrpCat.{u}
    (lisseEtaleTopology X) X.etaleTopology

/-- Abelian lower shriek is left adjoint to restriction. -/
abbrev lisseEtaleAbelianLowerShriek.adjunction (X : GroupoidsOver S)
    [AlgebraicStack X] :
    lisseEtaleAbelianLowerShriek X ⊣
      (lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
        (lisseEtaleTopology X) X.etaleTopology :=
  (lisseEtaleInclusion X).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (lisseEtaleTopology X) X.etaleTopology

/-- The unit `id ⟶ g^{-1} g_!` is an isomorphism on abelian sheaves. -/
theorem lisseEtaleAbelianLowerShriek_unit_app_isIso (X : GroupoidsOver S)
    [AlgebraicStack X] (F : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u}) :
    IsIso ((lisseEtaleAbelianLowerShriek.adjunction X).unit.app F) :=
  sorry

/-- The morphism of topoi
`g : Sh(X_flat,fppf) ⟶ Sh(X_fppf)` induced by the flat-fppf inclusion. -/
def flatFppfToposHom (X : GroupoidsOver S) [AlgebraicStack X] :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (inheritedFppfTopology X) (flatFppfTopology X) :=
  (flatFppfInclusion X).morphismOfTopoiInOfCocontinuous
    (flatFppfTopology X) (inheritedFppfTopology X)

/-- The underlying inverse image of `flatFppfToposHom` is the sheafified
cocontinuous pullback. -/
theorem flatFppfToposHom_inverseImage (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfToposHom X).inverseImage =
      (flatFppfInclusion X).sheafPullbackCocontinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) :=
  sorry

/-- The underlying direct image of `flatFppfToposHom` is the cocontinuous sheaf
pushforward. -/
theorem flatFppfToposHom_pushforward (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfToposHom X).pushforward =
      (flatFppfInclusion X).sheafPushforwardCocontinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) :=
  sorry

/-- The comparison from cocontinuous pullback to restriction along the
flat-fppf inclusion. -/
def flatFppfRestrictionComparison (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInclusion X).sheafPullbackCocontinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⟶
      (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) :=
  CocontinuousPullback.comparison.{u} (flatFppfInclusion X)
    (flatFppfTopology X) (inheritedFppfTopology X)

/-- Restriction along the flat-fppf inclusion identifies the cocontinuous
inverse image with continuous pushforward. -/
instance flatFppfRestrictionComparison.instIsIso
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsIso (flatFppfRestrictionComparison X) :=
  sorry

/-- Restriction along the flat-fppf inclusion is precomposition with the
opposite inclusion on underlying presheaves. -/
theorem flatFppfInclusion_restriction_spec (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
          (flatFppfTopology X) (inheritedFppfTopology X) ⋙
        sheafToPresheaf (flatFppfTopology X) (Type u) =
      sheafToPresheaf (inheritedFppfTopology X) (Type u) ⋙
        (whiskeringLeft _ _ (Type u)).obj (flatFppfInclusion X).op :=
  sorry

/-- Set-valued lower shriek `g_!^{Sh}` along the flat-fppf inclusion. -/
abbrev flatFppfLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    Sheaf (flatFppfTopology X) (Type u) ⥤
      Sheaf (inheritedFppfTopology X) (Type u) :=
  (flatFppfInclusion X).sheafPullback (Type u)
    (flatFppfTopology X) (inheritedFppfTopology X)

/-- Set-valued lower shriek is left adjoint to restriction. -/
abbrev flatFppfLowerShriek.adjunction (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfLowerShriek X ⊣
      (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) :=
  (flatFppfInclusion X).sheafAdjunctionContinuous (Type u)
    (flatFppfTopology X) (inheritedFppfTopology X)

/-- Restriction along the flat-fppf inclusion is left adjoint to cocontinuous
direct image. -/
abbrev flatFppfSheafAdjunctionCocontinuous (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⊣
      (flatFppfInclusion X).sheafPushforwardCocontinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) :=
  (flatFppfInclusion X).sheafAdjunctionCocontinuous (Type u)
    (flatFppfTopology X) (inheritedFppfTopology X)

/-- The unit `id ⟶ g^{-1} g_!^{Sh}` is an isomorphism on sheaves of sets. -/
theorem flatFppfLowerShriek_unit_app_isIso (X : GroupoidsOver S)
    [AlgebraicStack X] (F : Sheaf (flatFppfTopology X) (Type u)) :
    IsIso ((flatFppfLowerShriek.adjunction X).unit.app F) :=
  sorry

/-- The counit `g^{-1} g_* ⟶ id` is an isomorphism on sheaves of sets. -/
theorem flatFppfSheafAdjunctionCocontinuous_counit_app_isIso
    (X : GroupoidsOver S) [AlgebraicStack X]
    (F : Sheaf (flatFppfTopology X) (Type u)) :
    IsIso ((flatFppfSheafAdjunctionCocontinuous X).counit.app F) :=
  sorry

/-- Abelian lower shriek `g_!` along the flat-fppf inclusion. -/
abbrev flatFppfAbelianLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    Sheaf (flatFppfTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u} :=
  (flatFppfInclusion X).sheafPullback AddCommGrpCat.{u}
    (flatFppfTopology X) (inheritedFppfTopology X)

/-- Abelian lower shriek is left adjoint to restriction. -/
abbrev flatFppfAbelianLowerShriek.adjunction (X : GroupoidsOver S)
    [AlgebraicStack X] :
    flatFppfAbelianLowerShriek X ⊣
      (flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
        (flatFppfTopology X) (inheritedFppfTopology X) :=
  (flatFppfInclusion X).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (flatFppfTopology X) (inheritedFppfTopology X)

/-- The unit `id ⟶ g^{-1} g_!` is an isomorphism on abelian sheaves. -/
theorem flatFppfAbelianLowerShriek_unit_app_isIso (X : GroupoidsOver S)
    [AlgebraicStack X] (F : Sheaf (flatFppfTopology X) AddCommGrpCat.{u}) :
    IsIso ((flatFppfAbelianLowerShriek.adjunction X).unit.app F) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
