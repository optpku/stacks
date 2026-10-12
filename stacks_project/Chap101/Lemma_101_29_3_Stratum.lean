/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Defs.LinearOrder
public import stacks_project.Chap100.Lemma_100_4_7_Topology
public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# Points and remainders of locally closed gerbe strata

A locally closed substack `U ⊂ X` determines the subset `|U| ⊆ |X|` as the
image of `Points.map U.ι`. For a linearly ordered family of such substacks,
the remainder `T i` is the complement of the union of all strictly earlier
images of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyClosedSubstack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The underlying set of points of a locally closed substack, as the image of
`|U.Y| → |X|`. -/
def pointsSet (U : LocallyClosedSubstack X) : Set (Points X) :=
  Set.range (Points.map U.ι)

/-- `pointsSet U` is the range of `Points.map U.ι`. -/
theorem pointsSet_eq (U : LocallyClosedSubstack X) :
    U.pointsSet = Set.range (Points.map U.ι) :=
  sorry

/-- A point of `|X|` lies in `pointsSet U` if and only if it is the image of a
point of `|U.Y|`. -/
theorem mem_pointsSet (U : LocallyClosedSubstack X) {x : Points X} :
    x ∈ U.pointsSet ↔ ∃ y : Points U.Y, Points.map U.ι y = x :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyClosedSubstack

namespace AlgebraicGeometry.AlgebraicStack.GerbeStratification

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {I : Type (u + 1)} [LinearOrder I]

/-- The remainder `T i = |X| \ ⋃ i' < i, |U i'|` of a linearly ordered family of
locally closed substacks. -/
def remainder (U : I → LocallyClosedSubstack X) (i : I) : Set (Points X) :=
  (Set.univ : Set (Points X)) \ ⋃ i', ⋃ (_ : i' < i), (U i').pointsSet

/-- `remainder U i` is the complement in `|X|` of the union of `|U i'|` over
`i' < i`. -/
theorem remainder_def (U : I → LocallyClosedSubstack X) (i : I) :
    remainder U i =
      (Set.univ : Set (Points X)) \ ⋃ i', ⋃ (_ : i' < i), (U i').pointsSet :=
  sorry

/-- A point of `|X|` lies in `remainder U i` if and only if it lies in none of
the earlier strata `|U i'|` for `i' < i`. -/
theorem mem_remainder (U : I → LocallyClosedSubstack X) {i : I} {x : Points X} :
    x ∈ remainder U i ↔ ∀ i' < i, x ∉ (U i').pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicStack.GerbeStratification
