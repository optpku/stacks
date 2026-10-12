/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap84.Lemma_84_6_6_InverseImage
public import stacks_project.Chap84.Lemma_84_6_6_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.6.6

In the setup of Lemma 84.6.4, a finite morphism of algebraic spaces identifies
`a_Y⁻¹(R f_small,* K)` with `R f_big,fppf,* (a_X⁻¹ K)` on `D⁺(X_étale)` via the
canonical derived base-change map. Here `a_X = π_X ∘ ε_X` and `a_Y = π_Y ∘ ε_Y`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

/-- Lemma 84.6.6: in the setup of Lemma 84.6.4, if `f : X ⟶ Y` is a finite morphism of
algebraic spaces over a scheme `S`, then the canonical derived base-change map
identifies `a_Y⁻¹(R f_small,* K)` with `R f_big,fppf,* (a_X⁻¹ K)` for
`K` in `D⁺(X_étale)`, where `a_X = π_X ∘ ε_X` and `a_Y = π_Y ∘ ε_Y`. -/
@[stacks 0DGK]
theorem finite_derivedPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsFinite f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso (derivedBaseChangeApp f K) := sorry

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
