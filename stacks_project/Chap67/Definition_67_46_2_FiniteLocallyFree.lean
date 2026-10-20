/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap74.Lemma_74_11_29_Instances

/-!
# Finite locally free morphisms of algebraic spaces

A morphism of algebraic spaces is finite locally free when it is affine and the
direct image of its structure sheaf is a finite locally free module on the
target. Rank (also called degree) is the constant-rank refinement of that
module condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The pushforward structure module is the direct image of the structure sheaf. -/
theorem pushforwardStructureModule_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    AlgebraicGeometry.AlgebraicSpace.Hom.pushforwardStructureModule f =
      (Modules.pushforward f).obj (SheafOfModules.unit (structureSheaf X)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Hom

/-- The direct image of the structure sheaf along a morphism of algebraic spaces. -/
noncomputable abbrev CategoryTheory.NatTrans.pushforwardStructureModule {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : CategoryTheory.NatTrans X.functorOfPoints Y.functorOfPoints) :
    Y.Modules :=
  AlgebraicGeometry.AlgebraicSpace.Modules.pushforwardStructureModule f

#check (AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFreeOfRank :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → ℕ → Prop)
