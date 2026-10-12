/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Precomposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Precomposition for stacks in groupoids

This module packages precomposition from the Hom category of stacks in groupoids to the
ambient Hom category of groupoid-fibered categories.  The source of the comparison morphism
need not itself be a stack.

## Main declarations

* `CategoryTheory.StackOver.Groupoids.Hom.precomp` -- precomposition in the
  groupoid-fibered bicategory.
* `CategoryTheory.FiberedCategoryOver.Groupoids.Hom.IsLocalEquivalence.lift` -- the
  source-facing factorization through a local-equivalence presentation.
* `CategoryTheory.FiberedCategoryOver.Groupoids.Hom.IsStackification.lift` -- the same
  factorization directly from the stackification predicate.
* `CategoryTheory.FiberedCategoryOver.Groupoids.Hom.IsStackification.liftIsoUnique` -- the
  uniquely compatible comparison between two chosen factorizations.
* `CategoryTheory.StackOver.Groupoids.Hom.precomp_isEquivalence` -- the universal-property
  consequence for a local equivalence into a stack in groupoids.
* `CategoryTheory.FiberedCategoryOver.Groupoids.Hom.IsStackification.precomp_isEquivalence` --
  the same consequence from the descent-theoretic stackification predicate.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

namespace StackOver.Groupoids.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- Precompose a morphism of stacks in groupoids by a morphism of groupoid-fibered categories.
The codomain is ambient because the source `X` need not satisfy the stack condition. -/
@[stacks 0436 "precomposition into a groupoid stack"]
noncomputable abbrev precomp
    (Z : StackOver.Groupoids.{u, v, w, vS} J)
    {X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {Y : StackOver.Groupoids.{u, v, w, vS} J} (i : X ⟶ Y.toGroupoids) :
    (Y ⟶ Z) ⥤ (X ⟶ Z.toGroupoids) :=
  Bicategory.InducedBicategory.precompToAmbient Z i

/-- Precomposition into a stack in groupoids is an equivalence when the comparison morphism is
a local equivalence of groupoid-fibred categories. -/
@[stacks 0436 "Hom equivalence induced by a groupoid local equivalence"]
theorem precomp_isEquivalence
    (Z : StackOver.Groupoids.{u, v, w, vS} J)
    {X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {Y : StackOver.Groupoids.{u, v, w, vS} J} {i : X ⟶ Y.toGroupoids}
    (hi : FiberedCategoryOver.Groupoids.Hom.IsLocalEquivalence J i) :
    (precomp Z i).IsEquivalence := sorry

end StackOver.Groupoids.Hom

namespace FiberedCategoryOver.Groupoids.Hom.IsLocalEquivalence

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- A morphism from the source of a local-equivalence presentation to a stack in groupoids
factors through its stack target, up to an invertible `2`-cell. -/
@[stacks 0436 "factorization through a groupoid stackification"]
theorem lift
    {X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {Y Z : StackOver.Groupoids.{u, v, w, vS} J}
    {i : X ⟶ Y.toGroupoids} (hi : IsLocalEquivalence J i)
    (F : X ⟶ Z.toGroupoids) :
    ∃ G : Y ⟶ Z,
      Nonempty ((StackOver.Groupoids.Hom.precomp Z i).obj G ≅ F) := sorry

end FiberedCategoryOver.Groupoids.Hom.IsLocalEquivalence

namespace FiberedCategoryOver.Groupoids.Hom.IsStackification

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- A morphism from the source of a groupoid stackification to a stack in groupoids factors
through the stackification, up to an invertible `2`-cell. -/
@[stacks 0436 "factorization through a groupoid stackification"]
theorem lift
    {X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {Y Z : StackOver.Groupoids.{u, v, w, vS} J}
    {i : X ⟶ Y.toGroupoids} (hi : IsStackification J i)
    (F : X ⟶ Z.toGroupoids) :
    ∃ G : Y ⟶ Z,
      Nonempty ((StackOver.Groupoids.Hom.precomp Z i).obj G ≅ F) := sorry

/-- Two lifts through a groupoid stackification are related by a unique isomorphism compatible
with their chosen factorization cells. This is the typed groupoid-stack specialization of
`CartesianBasedFunctor.IsStackification.liftIsoUnique`. -/
@[stacks 0436 "unique comparison of groupoid-stackification lifts"]
theorem liftIsoUnique
    {X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {Y Z : StackOver.Groupoids.{u, v, w, vS} J}
    {i : X ⟶ Y.toGroupoids} (hi : IsStackification J i)
    {F : X ⟶ Z.toGroupoids}
    (G₁ G₂ : Y ⟶ Z)
    (α₁ : (StackOver.Groupoids.Hom.precomp Z i).obj G₁ ≅ F)
    (α₂ : (StackOver.Groupoids.Hom.precomp Z i).obj G₂ ≅ F) :
    ∃! β : G₁ ≅ G₂,
      (StackOver.Groupoids.Hom.precomp Z i).mapIso β ≪≫ α₂ = α₁ := sorry

/-- Precomposition into a stack in groupoids is an equivalence for a stackification morphism.
This is the direct bridge from the descent-theoretic predicate to the shared precomposition
owner. -/
@[stacks 0436 "Hom equivalence induced by a groupoid stackification"]
theorem precomp_isEquivalence
    {X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {Y : StackOver.Groupoids.{u, v, w, vS} J}
    {i : X ⟶ Y.toGroupoids} (hi : IsStackification J i)
    (Z : StackOver.Groupoids.{u, v, w, vS} J) :
    (StackOver.Groupoids.Hom.precomp Z i).IsEquivalence := sorry

end FiberedCategoryOver.Groupoids.Hom.IsStackification

end CategoryTheory
