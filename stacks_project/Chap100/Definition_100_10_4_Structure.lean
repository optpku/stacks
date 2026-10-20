/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Points
public import stacks_project.Chap100.Lemma_100_10_1_Points

/-!
# Algebraic stack structures on closed subsets

A closed subset of the points of an algebraic stack may carry many algebraic stack
structures, each realized by a closed substack with that underlying point-set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids (toFunctor)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

namespace ClosedSubstackStructure

variable {Z : Closeds (Points X)}

/-- The algebraic stack structure on `Z` determined by a closed substack with that
point-set. -/
def ofSubstack (W : ClosedSubstack X) (h : W.pointsSet = Z.carrier) :
    ClosedSubstackStructure Z :=
  ofProperty (toFunctor W.ι).essImage
    (@image_isClosed S W.Y X W.isAlgebraicStack inferInstance W.ι W.isClosedImmersion)
    ((@Substack.pointsSet_essImage S X W.Y inferInstance W.isAlgebraicStack
      W.ι W.isClosedImmersion).trans h)

/-- The closed substack presented by a canonical closed-substack structure. -/
def substack (T : ClosedSubstackStructure Z) : ClosedSubstack X where
  Y := T.Y
  ι := T.ι
  isAlgebraicStack := inferInstance
  isClosedImmersion := (spec T).1
  isStrictlyFull :=
    { full := by
        change T.val.ι.Full
        infer_instance
      faithful := by
        change T.val.ι.Faithful
        infer_instance }

/-- The underlying stack of a closed-substack structure is the stack of its realizing
closed substack. -/
theorem Y_eq (T : ClosedSubstackStructure Z) : T.Y = T.substack.Y :=
  rfl

/-- The inclusion of a closed-substack structure is the inclusion of its realizing
closed substack. -/
theorem ι_eq (T : ClosedSubstackStructure Z) : T.ι = T.substack.ι :=
  rfl

end ClosedSubstackStructure

end AlgebraicGeometry.AlgebraicStack
