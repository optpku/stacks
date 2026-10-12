/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_100_7_Adjunction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FppfEtale
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FppfEtale

/-- Lemma 59.100.7: for a scheme `X` and `K` in `D⁺(X_étale)`, the derived adjunction unit
`K ⟶ Ra_{X,*} (a_X⁻¹ K)` is an isomorphism, where
`a_X : Sh((Sch/X)_fppf) ⟶ Sh(X_étale)` is the composite `π_X ∘ ε_X`. -/
@[stacks 0DDT]
theorem plusAAdjunction_unit_isIso {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIso ((plusAAdjunction X).unit.app K) := sorry

end AlgebraicGeometry.Scheme.FppfEtale

end

end
