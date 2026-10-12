/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_27_12_RimSchlessinger
public import stacks_project.Chap98.Lemma_98_27_4_Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Rim-Schlessinger condition for the Artin contraction functor

In Situation 98.27.1 the contraction functor on locally Noetherian schemes
over `S` satisfies condition (RS).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Over

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Lemma 98.27.12: In Situation 98.27.1 the functor `σ.functor` satisfies the
Rim-Schlessinger condition (RS). -/
@[stacks 0GI6, instance]
instance instHasRimSchlessinger (σ : ContractionSituation S) :
    HasRimSchlessinger σ.functor := sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
