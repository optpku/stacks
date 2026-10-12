/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap82.Lemma_82_4_3_Length

/-!
# Length along a closed immersion of algebraic spaces

A quasi-coherent module on the source of a closed immersion has length `d` at a
point if and only if its pushforward has length `d` at the image point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 82.4.3: Let `S` be a scheme. Let `i : Y ⟶ X` be a closed immersion of
algebraic spaces over `S`. Let `G` be a quasi-coherent `𝒪_Y`-module. Let `y ∈ |Y|`
with image `Points.map i y ∈ |X|`. Let `d : ℕ∞`. Then `G` has length `d` at `y` if
and only if `(pushforward i).obj G` has length `d` at `Points.map i y`. -/
@[stacks 0EE3]
theorem hasLengthAt_pushforward_closedImmersion (i : Y ⟶ X) [IsClosedImmersion i]
    (G : Y.Modules) [G.IsQuasicoherent] (y : Points Y) (d : ℕ∞) :
    hasLengthAt G y d ↔ hasLengthAt ((pushforward i).obj G) (Points.map i y) d :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
