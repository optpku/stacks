/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Dimension functions after finite surjective descent

If a function on points of an algebraic space pulls back along a surjective
finite morphism to a dimension function, then it is itself a dimension function.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.25.6: Let `S` be a scheme. Let `f : Y ⟶ X` be a surjective finite
morphism of decent and locally Noetherian algebraic spaces. Let
`δ : Points X → ℤ` be a function. If `δ ∘ Points.map f` is a dimension
function, then `δ` is a dimension function. -/
@[stacks 0ED9]
theorem isDimensionFunction_of_comp_map {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [Surjective f] [IsFinite f] [IsDecent Y] [IsDecent X]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian X] {δ : Points X → ℤ}
    (hδ : IsDimensionFunction (δ ∘ Points.map f)) : IsDimensionFunction δ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
