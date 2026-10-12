/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving

/-!
# Limit preserving on objects, not limit preserving
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids

/-- Lemma 110.54.1: for a nonempty scheme `S` there exists a stack in groupoids
`p : 𝒳 ⟶ (Sch/S)_fppf` that is limit preserving on objects, while `𝒳` is not
limit preserving. -/
@[stacks 07Z1]
theorem exists_limitPreservingOnObjects_not_limitPreserving
    {S : Scheme.{u}} [Nonempty S] :
    ∃ (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u}
        (Scheme.fppfTopology.over S)),
      LimitPreservingOnObjects
          (baseProjection.{u + 1, u, u + 1} 𝒳.toGroupoids) ∧
        ¬ LimitPreserving 𝒳.toGroupoids := sorry

end AlgebraicGeometry.Groupoids
