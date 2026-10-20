/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.CategoryTheory.Functor.Derived.Model

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The derived category of abelian sheaves on the small étale site of a scheme. -/
abbrev Derived (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :=
  DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- Continuous direct image of small-universe abelian étale sheaves. -/
abbrev abelianDirectImage {X Z : Scheme.{u}} (i : Z ⟶ X) :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
    X.smallEtaleTopology Z.smallEtaleTopology

/-- The affine-presented inverse image of abelian étale sheaves is additive. -/
instance abelianInverseImage_additive {X Z : Scheme.{u}} (i : Z ⟶ X) :
    (abelianInverseImage i).Additive :=
  (abelianAdjunctionDirectImage i).left_adjoint_additive

/-- Inverse image of abelian étale sheaves preserves finite colimits. -/
instance abelianInverseImage_preservesFiniteColimits {X Z : Scheme.{u}} (i : Z ⟶ X) :
    PreservesFiniteColimits (abelianInverseImage i) :=
  @PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ (abelianInverseImage i)
    ((abelianAdjunctionDirectImage i).leftAdjoint_preservesColimits :
      PreservesColimitsOfSize.{u, u} (abelianInverseImage i))

/-- The affine-presented inverse image of abelian étale sheaves preserves finite limits. -/
instance abelianInverseImage_preservesFiniteLimits {X Z : Scheme.{u}} (i : Z ⟶ X) :
    PreservesFiniteLimits (abelianInverseImage i) :=
  @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    ((abelianAdjunctionDirectImage i).leftAdjointUniq
      (@Adjunction.ofIsRightAdjoint _ _ _ _ _
        (abelianAdjunctionDirectImage i).isRightAdjoint)).symm
    (@smallEtalePullbackAbelian_preservesFiniteLimits.{u}
      (fun {_ _} morphism ↦ (abelianAdjunctionDirectImage morphism).isRightAdjoint)
      _ _ i inferInstance inferInstance)

/-- A total right-derived model of an additive functor between abelian étale sheaf categories. -/
abbrev RightDerivedModel {X Z : Scheme.{u}}
    [HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasDerivedCategory.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [F.Additive] :=
  Functor.RightDerived.Model
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (DerivedCategory.Qh : HomotopyCategory _ (ComplexShape.up ℤ) ⥤ Derived Z)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

end AlgebraicGeometry.Scheme.Etale
