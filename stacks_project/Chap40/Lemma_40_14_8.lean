/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap39.Lemma_39_13_4_Groupoid
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Finite
import StacksCheckRecall

universe u

open AlgebraicGeometry

/- Lemma 40.14.8: if the source and target maps of a groupoid scheme are finite, then two
distinct points in the same orbit do not specialize from the first point to the second. -/
@[stacks 0ABG] #check
  (AlgebraicGeometry.GroupoidScheme.not_specializes_of_mem_orbit :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [IsFinite G.s.left] [IsFinite G.t.left] {u u' : G.U.left},
      u ≠ u' → u' ∈ G.t.left '' (G.s.left ⁻¹' {u}) → ¬ u ⤳ u')
