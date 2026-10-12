/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Local-ring dimension along locally quasi-finite morphisms

A locally quasi-finite morphism of algebraic spaces cannot increase the
dimension of the local ring at a point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.12.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a locally quasi-finite
morphism of algebraic spaces over `S`. Let `x` be a point of `X`. Then
`localRingDimAt x ≤ localRingDimAt (Points.map f x)`. -/
@[stacks 0ABW]
theorem localRingDimAt_le_of_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyQuasiFinite f] (x : Points X) :
    localRingDimAt x ≤ localRingDimAt (Points.map f x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
