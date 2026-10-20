/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotientPurity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.PuncturedSpectrum
open IsLocalRing

noncomputable section

universe u

/- Lemma 58.25.2: Let `(A, m)` be a Noetherian local ring and let `f ∈ m`.
Assume `A` is `f`-adically complete, `f` is a nonzerodivisor,
`H¹_m(A/fA)` and `H²_m(A/fA)` are finite `A`-modules, purity holds for
`(A_f)_p` for every maximal ideal `p` of `A_f`, and purity holds for `A`.
Then purity holds for `A/fA`. -/
@[stacks 0BPC] #check
  (AlgebraicGeometry.PuncturedSpectrum.hasPurity_principalQuotient_of_complete_localCohomology :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : maximalIdeal A)
    [IsAdicComplete (principalIdeal (f : A)) A]
    [Fact (IsRegular (f : A))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 1).obj
        (ModuleCat.of A (A ⧸ principalIdeal (f : A))))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 2).obj
        (ModuleCat.of A (A ⧸ principalIdeal (f : A))))]
    [Fact (hasPurityAtMaximalsAway f)]
    [HasPurity A],
    HasPurity (A ⧸ principalIdeal (f : A)))
