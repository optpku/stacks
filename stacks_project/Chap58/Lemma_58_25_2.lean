/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import stacks_project.Chap58.Lemma_58_24_1

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.PuncturedSpectrum
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (f : maximalIdeal A)

/-- Lemma 58.25.2: in Situation 58.19.1, if `A` is `f`-adically complete, `f` is a
nonzerodivisor, `H¹_m(A ⧸ fA)` and `H²_m(A ⧸ fA)` are finite `A`-modules, purity
holds at `(A_f)_p` for every maximal ideal `p` of `A_f`, and purity holds for `A`,
then purity holds for `A ⧸ principalIdeal f`. -/
@[stacks 0BPC, instance]
instance hasPurity_principalQuotient_of_complete_localCohomology
    [IsAdicComplete (principalIdeal f) A]
    [Fact (IsRegular (f : A))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 1).obj
        (ModuleCat.of A
          (A ⧸ (principalIdeal f • (⊤ : Submodule A A)))))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 2).obj
        (ModuleCat.of A
          (A ⧸ (principalIdeal f • (⊤ : Submodule A A)))))]
    [Fact (hasPurityAtMaximalsAway f)]
    [HasPurity A] :
    HasPurity (A ⧸ principalIdeal f) := sorry

end AlgebraicGeometry.PuncturedSpectrum
