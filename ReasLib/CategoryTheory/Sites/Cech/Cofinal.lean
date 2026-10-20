/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.Cech.Basic
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology vanishing from cofinal Čech systems

This file packages cofinal covering systems at the site level.  The owners are independent of
ringed spaces and numbered chapters: a system records covering and intersection closure, while
Čech acyclicity adds the coefficient-dependent vanishing condition.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe v u

namespace CategoryTheory.Sheaf.Cech

/-- A cofinal system of covers whose iterated Čech intersections remain in a chosen family of
objects. -/
@[stacks 03F9 "cofinal Cech covering systems"]
structure CofinalSystem
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ U : C, HasFiniteProducts (Over U)]
    (B : Set C) (Cov : ∀ U : C, Set (FormalCoproduct (Over U))) : Prop where
  coversTop :
    ∀ ⦃U : C⦄, U ∈ B → ∀ {cover : FormalCoproduct (Over U)},
      cover ∈ Cov U → (J.over U).CoversTop cover.obj
  intersections_mem :
    ∀ ⦃U : C⦄, U ∈ B → ∀ {cover : FormalCoproduct (Over U)},
      cover ∈ Cov U → ∀ n : ℕ, ∀ i : cechCoverIntersectionIndex cover n,
        cechCoverIntersectionObject cover n i ∈ B
  cofinal :
    ∀ ⦃U : C⦄, U ∈ B → ∀ ⦃ι : Type*⦄ (family : ι → Over U),
      (J.over U).CoversTop family →
        ∃ cover : FormalCoproduct (Over U),
          cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family)

namespace CofinalSystem

/-- A cover in a cofinal Čech system refines any given cover of the same object. -/
theorem exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ U : C, HasFiniteProducts (Over U)]
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct (Over U))}
    (hCov : CofinalSystem J B Cov)
    {U : C} (hU : U ∈ B) {ι : Type*} (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family) :
    ∃ cover : FormalCoproduct (Over U),
      cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family) := sorry

end CofinalSystem

/-- An abelian sheaf is Čech-acyclic on a cofinal system when every positive-degree Čech
cohomology object associated to a chosen cover is zero. -/
@[stacks 03F9 "Cech acyclicity on a cofinal covering system"]
structure IsAcyclic
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ U : C, HasFiniteProducts (Over U)]
    (F : Sheaf J AddCommGrpCat.{v}) (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct (Over U))) : Prop
    extends CofinalSystem J B Cov where
  isZero_cechCohomology :
    ∀ ⦃U : C⦄, U ∈ B → ∀ {cover : FormalCoproduct (Over U)},
      cover ∈ Cov U → ∀ {p : ℕ}, 0 < p →
        IsZero (cechCohomology U cover.obj ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) p)

namespace IsAcyclic

/-- Lemma 21.10.9 (03F9): positive-degree sheaf cohomology vanishes on every object covered by
a cofinal Čech-acyclic system. -/
@[stacks 03F9 "cohomology vanishing from a cofinal Cech-acyclic system"]
theorem isZero_cohomology
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ U : C, HasFiniteProducts (Over U)]
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {F : Sheaf J AddCommGrpCat.{v}} {B : Set C}
    {Cov : ∀ U : C, Set (FormalCoproduct (Over U))}
    (hF : IsAcyclic F B Cov) {U : C} (hU : U ∈ B) {p : ℕ} (hp : 0 < p) :
    IsZero (F.H' p U) := sorry

end IsAcyclic



end CategoryTheory.Sheaf.Cech
