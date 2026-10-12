/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import StacksCheckRecall

@[expose] public section

universe uA uσ

/- Lemma 27.8.8: Let `S` be a graded ring. The scheme `Proj(S)` is separated. -/
@[stacks 01MC] #check (AlgebraicGeometry.Proj.instIsSeparated :
  ∀ {σ : Type uσ} {A : Type uA} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜], (AlgebraicGeometry.Proj 𝒜).IsSeparated)
