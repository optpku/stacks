/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap67.Lemma_67_4_13
public import stacks_project.Chap79.«79_12_0_2»
public import stacks_project.Chap79.Remark_79_12_5_Algebra

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.CompactSupport

/-! # The compact-support comparison on the small étale site -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale Opposite
open AlgebraicGeometry.AlgebraicSpace.FinitePart
universe u

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.f2Coeff : AddCommGrpCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.constantF2 :
  ∀ (X : Scheme.{u}) [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}],
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.finitePartEtale :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Sheaf Y.smallEtaleTopology (Type u))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.finitePartEtale_obj_equiv :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale),
    (finitePartEtale f).obj.obj (op V) ≃
      Point (ofSchemeHom f) ((Scheme.Etale.forget Y).obj V))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.ofSection :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [AlgebraicGeometry.IsSeparated f] [LocallyQuasiFinite f] (V : Y.Etale),
    compactSupportSections f (constantF2 X) V →
      Point (ofSchemeHom f) ((Scheme.Etale.forget Y).obj V))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.lowerShriekF2Equiv :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [AlgebraicGeometry.IsSeparated f] [LocallyQuasiFinite f] (V : Y.Etale),
    (CategoryTheory.forget AddCommGrpCat.{u}).obj
      (((etaleLowerShriek f).obj (constantF2 X)).obj.obj (op V)) ≃
        (finitePartEtale f).obj.obj (op V))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.lowerShriekF2Iso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [AlgebraicGeometry.IsSeparated f] [LocallyQuasiFinite f],
    ((etaleLowerShriek f).obj (constantF2 X)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u} ≅ (finitePartEtale f).obj)
