/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtalePurity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.PuncturedSpectrum
open IsLocalRing

universe u

/- Lemma 58.24.2: let `A` be a Noetherian local ring and `f` an element of its
maximal ideal. If `A` is `f`-adically complete, `f` is a
nonzerodivisor, `H¹_m(A ⧸ fA)` and `H²_m(A ⧸ fA)` are finite `A`-modules, and
purity holds at `(A_f)_p` for every maximal ideal `p` of `A_f`, then the restriction
functor `FÉt_U ⟶ FÉt_{U₀}` identified with
`Scheme.finiteEtaleBaseChange (principalQuotientMap f)` is essentially
surjective. -/
@[stacks 0EKA] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_essSurj_of_complete_localCohomology_purity :
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
    [Fact (hasPurityAtMaximalsAway f)],
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).EssSurj)
