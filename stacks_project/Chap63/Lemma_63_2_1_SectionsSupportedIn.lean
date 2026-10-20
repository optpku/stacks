/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsSupportedIn

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

open AlgebraicGeometry.Scheme.Etale

#check (AlgebraicGeometry.Scheme.Etale.abelianSheafSectionsSupportedIn :
  ∀ {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (U : X.Etale) (Z : Set U.left), AddSubgroup (F.1.obj (op U)))

#check (AlgebraicGeometry.Scheme.Etale.mem_abelianSheafSectionsSupportedIn_iff :
  ∀ {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (U : X.Etale) (Z : Set U.left) (σ : F.1.obj (op U)),
    σ ∈ abelianSheafSectionsSupportedIn F U Z ↔
      (abelianSheafSectionSupport F U σ : Set U.left) ⊆ Z)

#check (AlgebraicGeometry.Scheme.Etale.restrictSupportedIn :
  ∀ {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {U U' : X.Etale} (φ : U' ⟶ U) (Z : Set U.left),
    abelianSheafSectionsSupportedIn F U Z →+
      abelianSheafSectionsSupportedIn F U' (φ.left ⁻¹' Z))

#check (AlgebraicGeometry.Scheme.Etale.restrictSupportedIn_apply :
  ∀ {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {U U' : X.Etale} (φ : U' ⟶ U) (Z : Set U.left)
    (σ : abelianSheafSectionsSupportedIn F U Z),
    (restrictSupportedIn F φ Z σ).val = F.1.map φ.op σ.val)
