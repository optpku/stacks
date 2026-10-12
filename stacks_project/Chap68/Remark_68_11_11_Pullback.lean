/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_17_7

/-!
# Unique lifts of points along elementary étale neighbourhoods

An elementary étale neighbourhood of the image of a point under a morphism of
decent algebraic spaces pulls back to a space with a unique point over the
given pair.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
variable (f : X ⟶ Y) {x : Points X} (V : Elementary Y (Points.map f x))

/-- A point of `pullback f V.obj.hom` lies over the pair `(x, V.obj.point)`. -/
def isLift (x' : Points (pullback f V.obj.hom)) : Prop :=
  Points.map (pullback.fst f V.obj.hom) x' = x ∧
    Points.map (pullback.snd f V.obj.hom) x' =
      ofOver.pointsEquiv V.obj.toOver V.obj.point

/-- The fibre condition `isLift` is the conjunction of the two projection
equations. -/
theorem isLift_iff (x' : Points (pullback f V.obj.hom)) :
    isLift f V x' ↔
      Points.map (pullback.fst f V.obj.hom) x' = x ∧
        Points.map (pullback.snd f V.obj.hom) x' =
          ofOver.pointsEquiv V.obj.toOver V.obj.point :=
  sorry

/-- Uniqueness of the fibre point of `pullback f V.obj.hom` over
`(x, V.obj.point)`. -/
theorem uniqueLift_eq {x₁ x₂ : Points (pullback f V.obj.hom)}
    (hx₁ : isLift f V x₁) (hx₂ : isLift f V x₂) :
    x₁ = x₂ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
