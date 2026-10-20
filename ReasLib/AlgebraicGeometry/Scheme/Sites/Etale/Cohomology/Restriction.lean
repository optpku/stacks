/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Leray
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.ExactSquare
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Base change carries the chosen terminal étale object to the terminal étale object. -/
def smallEtalePullback_obj_terminal {X Z : Scheme.{u}} (i : Z ⟶ X)
    [HasTerminal X.Etale] [HasTerminal Z.Etale] :
    (smallEtalePullback i).obj (terminal X.Etale) ≅ terminal Z.Etale :=
  PreservesTerminal.iso (MorphismProperty.Over.pullback @Etale ⊤ i)

/-- Restriction of abelian étale sheaves preserves finite limits. -/
instance etaleAbelianRestriction_preservesFiniteLimits {X Z : Scheme.{u}} (i : Z ⟶ X)
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    PreservesFiniteLimits ((smallEtalePullback i).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology Z.smallEtaleTopology) :=
  preservesFiniteLimits_of_natIso
    ((abelianAdjunctionDirectImage i).leftAdjointUniq
      (Adjunction.ofIsRightAdjoint
        ((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
          X.smallEtaleTopology Z.smallEtaleTopology)))

/-- Restriction of abelian étale sheaves preserves finite colimits. -/
instance etaleAbelianRestriction_preservesFiniteColimits {X Z : Scheme.{u}} (i : Z ⟶ X)
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    PreservesFiniteColimits ((smallEtalePullback i).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology Z.smallEtaleTopology) :=
  preservesFiniteColimits_of_natIso
    ((abelianAdjunctionDirectImage i).leftAdjointUniq
      (Adjunction.ofIsRightAdjoint
        ((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
          X.smallEtaleTopology Z.smallEtaleTopology)))

/-- Restriction of abelian étale sheaves is additive for the supplied abelian structures. -/
instance etaleAbelianRestriction_additive {X Z : Scheme.{u}} (i : Z ⟶ X)
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    ((smallEtalePullback i).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology Z.smallEtaleTopology).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction of abelian étale sheaves preserves homology. -/
instance etaleAbelianRestriction_preservesHomology {X Z : Scheme.{u}} (i : Z ⟶ X)
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    ((smallEtalePullback i).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology Z.smallEtaleTopology).PreservesHomology :=
  inferInstance

/-- The inverse-image adjunction unit induces restriction of abelian global sections. -/
def etaleAbelianSectionsRestrict {X Z : Scheme.{u}} (i : Z ⟶ X)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [HasTerminal X.Etale] [HasTerminal Z.Etale]
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale) ⟶
      etaleAbelianRestriction i ⋙
        siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale) where
  app F :=
    ((Adjunction.ofIsRightAdjoint
          ((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
            X.smallEtaleTopology Z.smallEtaleTopology)).unit.app F).hom.app
        (op (terminal X.Etale)) ≫
      ((etaleAbelianRestriction i).obj F).obj.map
        (op (smallEtalePullback_obj_terminal i).inv)
  naturality _ _ _ := sorry

section Cohomology

variable {X Z : Scheme.{u}} (i : Z ⟶ X)
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal X.Etale]
variable [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal Z.Etale]
variable [(siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive]
variable [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
    X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint]

/-- Exact inverse image induces restriction on étale cohomology in every degree. -/
def etaleCohomologyRestrict
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    etaleCohomology X F q ⟶
      etaleCohomology Z ((etaleAbelianRestriction i).obj F) q :=
  Functor.RightDerived.exactSquareApp
    (siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale))
    (siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale))
    ((smallEtalePullback i).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology Z.smallEtaleTopology) (𝟭 AddCommGrpCat.{u})
    (etaleAbelianSectionsRestrict i) q F

end Cohomology

end AlgebraicGeometry.Scheme.Etale
