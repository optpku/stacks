/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.Cech.DeltaFunctor
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.CategoryTheory.Sites.Family.Covering
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cofinal fixed-target Cech systems

This file packages the hypotheses of Lemma 21.10.9 without requiring finite products in every
slice category.  Each selected covering family carries exactly the iterated fibre-product
witnesses used by its own Cech nerve.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf.Cech.FixedTarget

/-- A covering family together with the iterated fibre products needed for its fixed-target
Cech nerve. -/
@[stacks 03F9 "fixed-target Cech cover"]
structure Cover {C : Type u} [Category.{v} C] (U : C) where
  /-- The underlying indexed family over `U`. -/
  toFormalCoproduct : FormalCoproduct.{w} (Over U)
  /-- The selected family has all products used by its Cech nerve. -/
  [hasIteratedFiberProducts :
    HasIteratedFiberProducts toFormalCoproduct.obj]

attribute [instance] Cover.hasIteratedFiberProducts

/-- The indexed family underlying a fixed-target Cech cover. -/
@[stacks 03F9 "underlying family of a fixed-target Cech cover"]
abbrev Cover.family {C : Type u} [Category.{v} C] {U : C} (cover : Cover.{w} U) :
    cover.toFormalCoproduct.I → Over U :=
  cover.toFormalCoproduct.obj

/-- The degree-`n` indexing type of the intersections of a fixed-target Cech cover. -/
@[stacks 03F9 "intersection indices of a fixed-target Cech cover"]
abbrev Cover.index {C : Type u} [Category.{v} C] {U : C} (cover : Cover.{w} U)
    (n : ℕ) :=
  (familyPower cover.family n).I

/-- The underlying site object of one iterated intersection in a fixed-target Cech cover. -/
@[stacks 03F9 "intersection object of a fixed-target Cech cover"]
abbrev Cover.intersection {C : Type u} [Category.{v} C] {U : C} (cover : Cover.{w} U)
    (n : ℕ) (i : cover.index n) : C :=
  ((familyPower cover.family n).obj i).left

/-- A cofinal collection of fixed-target covers whose iterated intersections remain in a chosen
family of site objects. -/
@[stacks 03F9 "cofinal fixed-target Cech covering system"]
structure CofinalSystem
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Set C) (Cov : ∀ U : C, Set (Cover.{w} U)) : Prop where
  /-- Every selected family is a cover. -/
  coversTop : ∀ ⦃U : C⦄ {cover : Cover.{w} U},
    cover ∈ Cov U → (J.over U).CoversTop cover.family
  /-- The target of every selected cover belongs to `B`. -/
  target_mem : ∀ ⦃U : C⦄ {cover : Cover.{w} U}, cover ∈ Cov U → U ∈ B
  /-- Every iterated intersection of a selected cover remains in `B`. -/
  intersections_mem : ∀ ⦃U : C⦄ {cover : Cover.{w} U},
    cover ∈ Cov U → ∀ n : ℕ, ∀ i : cover.index n, cover.intersection n i ∈ B
  /-- The selected covers are cofinal among all covers of each object in `B`. -/
  cofinal : ∀ ⦃U : C⦄, U ∈ B → ∀ (family : FormalCoproduct.{w} (Over U)),
    (J.over U).CoversTop family.obj →
      ∃ cover : Cover.{w} U,
        cover ∈ Cov U ∧ Nonempty (cover.toFormalCoproduct ⟶ family)

namespace CofinalSystem

/-- A cover in a fixed-target cofinal system refines any given cover of the same object. -/
theorem exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {B : Set C} {Cov : ∀ U : C, Set (Cover.{w} U)}
    (hCov : CofinalSystem J B Cov) {U : C} (hU : U ∈ B)
    (family : FormalCoproduct.{w} (Over U)) (hfamily : (J.over U).CoversTop family.obj) :
    ∃ cover : Cover.{w} U,
      cover ∈ Cov U ∧ Nonempty (cover.toFormalCoproduct ⟶ family) := sorry

end CofinalSystem

/-- A sheaf is Cech-acyclic on a fixed-target cofinal system when every selected cover has zero
positive-degree fixed-target Cech cohomology. -/
@[stacks 03F9 "acyclicity on a fixed-target cofinal Cech system"]
structure IsAcyclic
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasProducts.{w} AddCommGrpCat.{max u v}]
    (F : Sheaf J AddCommGrpCat.{max u v}) (B : Set C)
    (Cov : ∀ U : C, Set (Cover.{w} U)) : Prop
    extends CofinalSystem J B Cov where
  /-- Positive fixed-target Cech cohomology vanishes on every selected cover. -/
  isZero_cechCohomology : ∀ ⦃U : C⦄ {cover : Cover.{w} U},
    cover ∈ Cov U → ∀ {p : ℕ}, 0 < p →
      IsZero (CategoryTheory.Cech.FixedTarget.cohomology cover.family
        ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj F) p)

namespace IsAcyclic

/-- Lemma 21.10.9 (03F9): fixed-target Cech acyclicity on a cofinal covering system implies
positive-degree sheaf-cohomology vanishing. -/
@[stacks 03F9 "cohomology vanishing from fixed-target cofinal Cech acyclicity"]
theorem isZero_cohomology
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasProducts.{w} AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    {F : Sheaf J AddCommGrpCat.{max u v}} {B : Set C}
    {Cov : ∀ U : C, Set (Cover.{w} U)}
    (hF : IsAcyclic F B Cov) {U : C} (hU : U ∈ B) {p : ℕ} (hp : 0 < p) :
    IsZero (Sheaf.cohomologyOverObject F U p) := sorry

end IsAcyclic

end CategoryTheory.Sheaf.Cech.FixedTarget
