module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Change of ideals on adic completions

The canonical ring homomorphism `AdicCompletion I R →+* AdicCompletion J R`
induced by an inclusion `I ≤ J`, specialized to `J = I.radical`.
-/

@[expose] public section

noncomputable section

universe u

open AdicCompletion

namespace AdicCompletion

/-- The stagewise comparison `R ⧸ I ^ n →+* R ⧸ J ^ n` of inverse-limit
coordinates, for `I ≤ J`. -/
def mapOfLeFamily {R : Type u} [CommRing R] {I J : Ideal R} (hIJ : I ≤ J)
    (n : ℕ) : AdicCompletion I R →+* R ⧸ J ^ n :=
  (Ideal.Quotient.factor (Ideal.pow_right_mono hIJ n)).comp (evalₐ I n).toRingHom

/-- Stagewise factor maps `R ⧸ I ^ n →+* R ⧸ J ^ n` are compatible with the
inverse-limit transition maps of the `J`-adic completion. -/
theorem mapOfLe_family_compat {R : Type u} [CommRing R] {I J : Ideal R}
    (hIJ : I ≤ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (mapOfLeFamily hIJ n) =
      mapOfLeFamily hIJ m :=
  sorry

/-- The canonical ring homomorphism from the `I`-adic completion to the
`J`-adic completion induced by `I ≤ J`. -/
def mapOfLe {R : Type u} [CommRing R] {I J : Ideal R} (hIJ : I ≤ J) :
    AdicCompletion I R →+* AdicCompletion J R :=
  liftRingHom J (mapOfLeFamily hIJ) (mapOfLe_family_compat hIJ)

/-- The source comparison from the `I`-adic completion to the `√I`-adic
completion. -/
def mapOfRadical {R : Type u} [CommRing R] (I : Ideal R) :
    AdicCompletion I R →+* AdicCompletion I.radical R :=
  mapOfLe I.le_radical

/-- Evaluating `mapOfLe` at the `n`-th inverse-limit coordinate recovers the
stagewise factor map `R ⧸ I ^ n →+* R ⧸ J ^ n`. -/
theorem mapOfLe_evalₐ {R : Type u} [CommRing R] {I J : Ideal R} (hIJ : I ≤ J)
    (n : ℕ) :
    (evalₐ J n).toRingHom.comp (mapOfLe hIJ) =
      (Ideal.Quotient.factor (Ideal.pow_right_mono hIJ n)).comp
        (evalₐ I n).toRingHom :=
  sorry

/-- `mapOfLe` intertwines the canonical maps from the uncompleted ring. -/
theorem mapOfLe_comp_of {R : Type u} [CommRing R] {I J : Ideal R} (hIJ : I ≤ J) :
    (mapOfLe hIJ).comp (algebraMap R (AdicCompletion I R)) =
      algebraMap R (AdicCompletion J R) :=
  sorry

/-- The comparison associated to `I ≤ I` is the identity. -/
theorem mapOfLe_id {R : Type u} [CommRing R] {I : Ideal R} :
    mapOfLe (le_rfl : I ≤ I) = RingHom.id (AdicCompletion I R) :=
  sorry

end AdicCompletion

