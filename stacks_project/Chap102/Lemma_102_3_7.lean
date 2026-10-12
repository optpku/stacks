/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import stacks_project.Chap102.Definition_102_3_1_LimitPreserving
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap107.Situation_107_2_1_Instances

/-!
# Algebraic stacks locally of finite presentation are limit preserving

An algebraic stack over a scheme `S` whose structure morphism is locally of
finite presentation is limit preserving in the sense of Artin's Axioms
Definition 98.11.1. Equivalently, the structure morphism itself is limit
preserving.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- Lemma 102.3.7: Let `S` be a scheme. Let `𝒳` be an algebraic stack over `S`.
If `𝒳 ⟶ S` is locally of finite presentation, then `𝒳` is limit preserving
in the sense of Artin's Axioms, Definition 98.11.1 (equivalently: the morphism
`𝒳 ⟶ S` is limit preserving). -/
@[stacks 0CMX]
instance toLimitPreserving {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation (baseProjection.{u + 1, u, u + 1} X)] :
    Groupoids.LimitPreserving X := sorry

/-- The structure morphism of an algebraic stack locally of finite presentation
over `S` is limit preserving as a 1-morphism of categories fibred in groupoids. -/
instance toHomLimitPreserving {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation (baseProjection.{u + 1, u, u + 1} X)] :
    Groupoids.Hom.LimitPreserving
      (baseProjection.{u + 1, u, u + 1} X) := sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

namespace AlgebraicGeometry.Groupoids.LimitPreserving

/-- A category fibred in groupoids over `(Sch/S)_fppf` is limit preserving if and
only if its structure morphism to `(Sch/S)_fppf` is limit preserving. -/
theorem iff_baseProjection {S : Scheme.{u}} (X : GroupoidsOver S) :
    LimitPreserving X ↔
      Hom.LimitPreserving (baseProjection.{u + 1, u, u + 1} X) := sorry

end AlgebraicGeometry.Groupoids.LimitPreserving
