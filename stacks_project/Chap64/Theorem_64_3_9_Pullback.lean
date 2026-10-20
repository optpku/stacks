/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.IteratedRelative.Basic
public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»
public import stacks_project.Chap64.Lemma_64_3_2_Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Geometric
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Frobenius

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

noncomputable section

/- Geometric Frobenius pullback on geometric étale cohomology. -/
#check (AlgebraicGeometry.SchemeOverField.geometricFrobeniusEtaleHq :
  ∀ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [∀ Z : Scheme.{u},
      HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ),
    geometricEtaleHq X F j ⟶ geometricEtaleHq X F j)
