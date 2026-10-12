/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.IdealPowerTorsion
import StacksCheckRecall

/-!
# Lemma 15.89.9

@stack 0BNK
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/- Lemma 15.89.9 (0BNK): compatible isomorphisms on all positive
ideal-power quotients make the canonical tensor unit bijective on every
ideal-power torsion module.  The reusable owner uses the library orientation
`M ⟶ S ⊗[R] M`, canonically identified by tensor symmetry with the source's
`M ⟶ M ⊗[R] S`. -/
@[stacks 0BNK "ideal-power torsion tensor base change"]
#check fun {R : Type u} [CommRing R] {R' : Type v} [CommRing R'] [Algebra R R']
    (I : Ideal R) {M : Type w} [AddCommMonoid M] [Module R M]
    (hM : Module.IsIdealPowerTorsion I M)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) ↦
  (tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
      (R' := R') I hM hquot :
    Function.Bijective (TensorProduct.mk R R' M 1))

/- Lemma 15.89.9 (0BNK), completion quotient comparison. -/
@[stacks 0BNK "adic completion quotient map"]
#check fun {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) ↦
  (adicCompletion_quotientMap_bijective I hI n :
    Function.Bijective
      (Ideal.quotientMap
        ((I ^ n).map (algebraMap R (AdicCompletion I R)))
        (algebraMap R (AdicCompletion I R))
        Ideal.le_comap_map))

/- Lemma 15.89.9 (0BNK), completion specialization of tensor base change. -/
@[stacks 0BNK "adic completion tensor base change"]
#check fun {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type w} [AddCommMonoid M] [Module R M]
    (hI : I.FG) (hM : Module.IsIdealPowerTorsion I M) ↦
  (tensorAdicCompletion_bijective_of_isIdealPowerTorsion I hI hM :
    Function.Bijective (TensorProduct.mk R (AdicCompletion I R) M 1))
