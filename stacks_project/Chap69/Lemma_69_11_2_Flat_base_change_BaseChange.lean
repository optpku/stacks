/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square.Exact
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_21_3
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.FlatBaseChange

/-! # Compatibility for module base-change comparisons -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor
open Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

variable {X' X Y' Y : AlgebraicSpace S}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The underived base-change 2-cell `g^* f_* ⟶ f'_* (g')^*` of module functors, as the mate of
the cartesian pullback square. -/
abbrev pushforwardBaseChangeNatTrans (h_cart : IsPullback g' f' f g) :
    pushforward f ⋙ pullback g ⟶ pullback g' ⋙ pushforward f' :=
  Modules.baseChange h_cart.w

end AlgebraicGeometry.AlgebraicSpace.Modules
