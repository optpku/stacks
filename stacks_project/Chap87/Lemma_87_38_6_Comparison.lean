/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap87.Lemma_87_38_5_Completion

/-!
# Canonical comparison of completions along a closed subspace

The completion `completionAlongSubspace Z.ι` along a closed subspace maps
canonically to the completion `completionAlong X Z.pointsCloseds` along the
underlying closed set `T = |Z|`, by the identity on underlying Yoneda sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The closed set `T = |Z|` of points of `X` underlying a closed subspace. -/
def pointsCloseds {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) :
    Closeds (Points X) where
  carrier := Z.pointsSet
  isClosed' := isClosed_pointsSet Z

/-- The carrier of `pointsCloseds Z` is `Z.pointsSet`. -/
theorem pointsCloseds_carrier {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :
    (Z.pointsCloseds : Set (Points X)) = Z.pointsSet :=
  sorry

/-- A point of `|X|` lies in `pointsCloseds Z` if and only if it lies in `|Z|`. -/
theorem mem_pointsCloseds {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) {x : Points X} :
    x ∈ Z.pointsCloseds ↔ x ∈ Z.pointsSet :=
  sorry

end ClosedSubspace

/-- A Yoneda section of `X` that fppf-locally factors through an infinitesimal
neighbourhood of `Z` has image of points contained in `|Z|`. -/
theorem mapsInto_of_fppfLocallyFactorsThroughNeighbourhood
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    {U : (Over S)ᵒᵖ} {x : X.functorOfPoints.obj U}
    (hx : fppfLocallyFactorsThroughNeighbourhood Z.ι x) :
    mapsInto (Z.pointsCloseds : Set (Points X)) x :=
  sorry

namespace completionAlongSubspace

/-- The canonical comparison `completionAlongSubspace Z.ι ⟶ completionAlong X Z.pointsCloseds`
from the completion along a closed subspace to the completion along `T = |Z|`.
On underlying Yoneda sections this is the identity. -/
def toCompletionAlong {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) :
    completionAlongSubspace Z.ι ⟶ completionAlong X Z.pointsCloseds where
  app _ :=
    ofHom fun x ↦
      ⟨x.1, mapsInto_of_fppfLocallyFactorsThroughNeighbourhood Z x.2⟩
  naturality := sorry

/-- The comparison `toCompletionAlong Z` is a morphism over `X.functorOfPoints`. -/
theorem toCompletionAlong_comp_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :
    toCompletionAlong Z ≫ completionAlong.ι X Z.pointsCloseds = ι Z.ι :=
  sorry

/-- On sections, `toCompletionAlong Z` is the identity of the underlying map into `X`. -/
theorem toCompletionAlong_app {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (U : (Over S)ᵒᵖ)
    (x : (completionAlongSubspace Z.ι).obj U) :
    (completionAlong.ι X Z.pointsCloseds).app U ((toCompletionAlong Z).app U x) =
      (ι Z.ι).app U x :=
  sorry

end completionAlongSubspace

end AlgebraicGeometry.AlgebraicSpace
