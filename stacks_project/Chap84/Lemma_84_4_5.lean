/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap84.Lemma_84_4_5_Comparison

/-!
# Lemma 84.4.5

Proper base change for stalks of sheaves of sets at a geometric point of an
algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 84.4.5: if `f : Y ⟶ X` is a proper morphism of algebraic spaces over a
scheme `S` and `xbar` is a geometric point of `X`, then for every sheaf of sets
`F` on `Y_étale` the canonical map `(f_* F)_xbar ⟶ Γ(Y_xbar, F_xbar)` is
bijective, where `Y_xbar` is the geometric fibre `pullback f xbar.hom` and
`F_xbar` is `geometricFiberSheaf f xbar F`. -/
@[stacks 0DG1]
theorem smallEtalePushforwardStalk_bijective_of_proper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Proper f]
    (xbar : GeometricPoint X)
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    Function.Bijective
      (smallEtalePushforwardStalkToGeometricFiberSections f xbar F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
