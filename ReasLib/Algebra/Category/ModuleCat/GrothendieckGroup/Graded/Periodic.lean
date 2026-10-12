/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Graded
public import ReasLib.RingTheory.Polynomial.Numerical.Periodic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Eventually quasi-polynomial Grothendieck classes of graded pieces

This leaf combines the generic K0 class-function owner with the generic eventually
quasi-polynomial predicate.  Keeping it separate prevents the basic graded K0 API from importing asymptotic
polynomial infrastructure.
-/

@[expose] public section

noncomputable section

universe u v w

namespace CategoryTheory.ModuleCat.K0

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜] [IsNoetherianRing S]
variable (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M]

/- API design: the conclusion is stated on `gradedPieceClass_of_isNoetherian`, so finite type is
derived inside the concrete data owner and is not repeated as a theorem hypothesis. -/

/-- The K0-valued class function of a finite module over a Noetherian graded algebra is eventually
quasi-polynomial. -/
@[stacks 02CD "eventually quasi-polynomial Noetherian graded-piece class"]
theorem gradedPieceClass_eventuallyQuasiPolynomial :
    EventuallyQuasiPolynomial (gradedPieceClass_of_isNoetherian 𝒜 ℳ) := sorry

end CategoryTheory.ModuleCat.K0
