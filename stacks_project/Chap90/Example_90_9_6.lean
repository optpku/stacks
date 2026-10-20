module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Frobenius
import StacksCheckRecall

/-!
# An explicit smooth object of `Ĉ_Λ` for a purely inseparable residue extension

For a prime `p` and `n : ℕ`, with `Λ = F_p(t_1, …, t_n)` and
`k = F_p(x_1, …, x_n)` via `t_i ↦ x_i^p`, the `I`-adic completion
`R = Λ[x_1, …, x_n]^∧_(x_i^p - t_i)` is an object of `Ĉ_Λ` as in
Lemma 90.9.5. Every smooth complete local object for this residue extension has
dimension at least `n`.
-/

@[expose] public section

open CategoryTheory IsLocalRing Algebra.H1Cotangent KaehlerDifferential
open CompleteLocalAlgCat MvRatFunc.Frobenius

noncomputable section

/- Example 90.9.6: the explicit Frobenius completion is a smooth complete local
object, and no smooth complete local object for this residue extension has
dimension smaller than the number of coordinates. -/
@[stacks 06SN] #check (CompleteLocalAlgCat.formallySmooth_pthPowerAdicCompletion :
  ∀ (n p : ℕ) [Fact p.Prime],
    (algebraMap (baseField n p) (pthPowerAdicCompletion n p).carrier).formally_smooth_for_adic
      (IsLocalRing.maximalIdeal (pthPowerAdicCompletion n p).carrier))

#check (CompleteLocalAlgCat.pthPowerAdicCompletion :
  ∀ (n p : ℕ) [Fact p.Prime], CompleteLocalAlgCat (baseField n p) (functionField n p))

#check (CompleteLocalAlgCat.pthPowerAdicCompletion_carrier :
  ∀ (n p : ℕ) [Fact p.Prime],
    (pthPowerAdicCompletion n p).carrier =
      AdicCompletion (pthPowerIdeal n p) (MvPolynomial (Fin n) (baseField n p)))

#check (MvRatFunc.Frobenius.pthPowerIdeal_eq_span :
  ∀ (n p : ℕ) [Fact p.Prime],
    pthPowerIdeal n p = Ideal.span (Set.range (pthPowerGen n p)))

#check (MvRatFunc.Frobenius.algebraMap_X :
  ∀ (n p : ℕ) [Fact p.Prime] (index : Fin n),
    algebraMap (baseField n p) (functionField n p) (baseCoordinate n p index) =
      coordinate n p index ^ p)

#check (CompleteLocalAlgCat.pthPowerAdicCompletion_residueFieldIso :
  ∀ (n p : ℕ) [Fact p.Prime],
    (pthPowerAdicCompletion n p).residueFieldIso = MvRatFunc.Frobenius.residueFieldIso n p)

#check (CompleteLocalAlgCat.instIsSmooth_restrictedCoyoneda_pthPowerAdicCompletion :
  ∀ (n p : ℕ) [Fact p.Prime],
    Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda (pthPowerAdicCompletion n p))))

#check (CompleteLocalAlgCat.bijective_toKerCotangent_pthPowerAdicCompletion :
  ∀ (n p : ℕ) [Fact p.Prime],
    Function.Bijective
      (toKerCotangent (baseField n p) (pthPowerAdicCompletion n p).carrier
        (functionField n p) (algebraMap_surjective (pthPowerAdicCompletion n p))))

#check (CompleteLocalAlgCat.bijective_mapBaseChange_pthPowerAdicCompletion :
  ∀ (n p : ℕ) [Fact p.Prime],
    Function.Bijective
      (mapBaseChange (baseField n p) (pthPowerAdicCompletion n p).carrier (functionField n p)))

#check (CompleteLocalAlgCat.le_ringKrullDim_of_formallySmooth_frobenius :
  ∀ (n p : ℕ) [Fact p.Prime] (R : CompleteLocalAlgCat (baseField n p) (functionField n p)),
    (algebraMap (baseField n p) R.carrier).formally_smooth_for_adic
      (IsLocalRing.maximalIdeal R.carrier) →
    (n : WithBot ℕ∞) ≤ ringKrullDim R.carrier)

#check (CompleteLocalAlgCat.le_ringKrullDim_pthPowerAdicCompletion :
  ∀ (n p : ℕ) [Fact p.Prime],
    (n : WithBot ℕ∞) ≤ ringKrullDim (pthPowerAdicCompletion n p).carrier)
