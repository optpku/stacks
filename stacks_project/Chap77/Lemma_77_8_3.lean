/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.LinearMap.CoefficientIdeal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 77.8.3

If `u : M →ₗ[A] N` is an `A`-module map and `N` is projective, there is an ideal
`I ⊆ A` such that for every ring map `φ : A → B`, `u ⊗ 1 : M ⊗[A] B → N ⊗[A] B`
is zero iff `φ(I) = 0`. The witnessing ideal is `LinearMap.coefficientIdeal`.
-/

universe uR uM uN uS

/- Lemma 77.8.3 -/
@[stacks 083L]
#check (LinearMap.exists_ideal_baseChange_eq_zero_iff :
  ∀ {R : Type uR} [CommRing R] {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N] [Module.Projective R N]
    (f : M →ₗ[R] N),
    ∃ I : Ideal R, ∀ (S : Type uS) [CommRing S] [Algebra R S],
      f.baseChange S = 0 ↔ I.map (algebraMap R S) = ⊥)
