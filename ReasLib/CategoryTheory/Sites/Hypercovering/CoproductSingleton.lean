/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.CoproductSingleton
public import ReasLib.CategoryTheory.Sites.Hypercovering.Constructors
import Mathlib.Tactic.CrossRefAttribute

/-!
# Singleton-coproduct replacements of fixed-target hypercoverings

For a hypercovering whose source family has a coproduct in every simplicial degree, this file
constructs the simplicial singleton family on those coproducts.  Pullback compatibility makes the
construction commute with matching objects, while cover preservation transfers the covering
conditions.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

namespace Hypercovering

namespace CoproductSingleton

variable {X : C}

/-- The simplicial fixed-target family obtained by replacing every degree of `K` with the
singleton family on the coproduct of its source objects. -/
abbrev simplicial (K : Hypercovering.{w} J X)
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.toSimplicialObject.obj Δ).obj i).left)] :
    SimplicialObject (SR(C, X)) :=
  FormalCoproduct.Over.Simplicial.coproductSingleton K.toSimplicialObject

/-- The coproduct inclusions assemble into the canonical simplicial map from `K` to its
singleton-coproduct replacement. -/
abbrev comparison (K : Hypercovering.{w} J X)
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.toSimplicialObject.obj Δ).obj i).left)] :
    K.toSimplicialObject ⟶ simplicial K :=
  FormalCoproduct.Over.Simplicial.toCoproductSingleton K.toSimplicialObject

/-- Cover preservation transfers the degree-zero covering condition to the singleton-coproduct
replacement. -/
theorem zero_isCovering
    [FormalCoproduct.CoproductSingleton.PreservesCovering.{w} J]
    (K : Hypercovering.{w} J X)
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.toSimplicialObject.obj Δ).obj i).left)] :
    ((simplicial K).obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X := sorry

/-- Pullback compatibility and cover preservation transfer every matching-map covering condition
to the singleton-coproduct replacement. -/
theorem succ_isCovering
    [FormalCoproduct.Over.CoproductSingleton.PullbackCompatible.{w} X]
    [FormalCoproduct.CoproductSingleton.PreservesCovering.{w} J]
    (K : Hypercovering.{w} J X)
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.toSimplicialObject.obj Δ).obj i).left)] :
    ∀ n : ℕ,
      SemiRepresentableFamily.OverFamily.covering J
        (SimplicialObject.matchingMap (simplicial K) n) := sorry

end CoproductSingleton

/-- Remark 25.12.9 (0DB2): replace each degree of a fixed-target hypercovering by the singleton
family on the coproduct of its source objects, assuming coproducts commute with pullbacks and
covering family morphisms induce covering arrows on coproducts. -/
@[stacks 0DB2 "singleton-coproduct replacement of a fixed-target hypercovering"]
def coproductSingleton
    {X : C}
    [FormalCoproduct.Over.CoproductSingleton.PullbackCompatible.{w} X]
    [FormalCoproduct.CoproductSingleton.PreservesCovering.{w} J]
    (K : Hypercovering.{w} J X)
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.toSimplicialObject.obj Δ).obj i).left)] :
    Hypercovering.{w} J X :=
  ofSimplicial (CoproductSingleton.simplicial K)
    (CoproductSingleton.zero_isCovering K)
    (CoproductSingleton.succ_isCovering K)

/-- The simplicial object underlying `coproductSingleton` is the canonical fixed-target
singleton-coproduct replacement. -/
@[simp] theorem coproductSingleton_toSimplicialObject
    {X : C}
    [FormalCoproduct.Over.CoproductSingleton.PullbackCompatible.{w} X]
    [FormalCoproduct.CoproductSingleton.PreservesCovering.{w} J]
    (K : Hypercovering.{w} J X)
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.toSimplicialObject.obj Δ).obj i).left)] :
    (coproductSingleton K).toSimplicialObject =
      CoproductSingleton.simplicial K := sorry

end Hypercovering

end CategoryTheory
