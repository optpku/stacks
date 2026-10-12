/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_17_1_Difference
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

/- Lemma 76.17.1: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `X ⊂ X'` and `Y ⊂ Y'` be two first-order thickenings of algebraic spaces
over `B`. Let `(a, a'), (b, b') : (X ⊂ X') ⟶ (Y ⊂ Y')` be two morphisms of
thickenings over `B`. Assume that `a = b`, and the two maps
`a^* C_{Y/Y'} ⟶ C_{X/X'}` (Lemma 76.5.3) are equal. Then the map
`(a')^♯ - (b')^♯` factors as `𝒪_{Y'} ⟶ 𝒪_Y ⟶^D a_* C_{X/X'} ⟶ a_* 𝒪_{X'}`
where `D` is an `𝒪_B`-derivation. -/
@[stacks 0618] #check exists_differenceDerivation
