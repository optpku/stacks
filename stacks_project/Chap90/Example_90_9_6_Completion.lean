module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal
public import stacks_project.Chap90.Example_90_9_6_FunctionField

/-!
# The `I`-adic completion `Λ[x_1, …, x_n]^∧_I`

For the purely inseparable pair `Λ = F_p(t_1, …, t_n) → k = F_p(x_1, …, x_n)`,
the explicit object of `Ĉ_Λ` is the completion of `Λ[x_1, …, x_n]` at
`I = (x_1^p - t_1, …, x_n^p - t_n)`, with residue identification to `k`.
-/

@[expose] public section

open MvPolynomial IsLocalRing PurelyInseparable

noncomputable section

namespace PurelyInseparable

/-- The generator `X i ^ p - C (t i)` of the defining ideal. -/
def pthPowerGen (n p : ℕ) [Fact p.Prime] (i : Fin n) :
    MvPolynomial (Fin n) (lambdaField n p) :=
  X i ^ p - C (t n p i)

/-- The ideal `I = (x_1^p - t_1, …, x_n^p - t_n)` in `Λ[x_1, …, x_n]`. -/
def pthPowerIdeal (n p : ℕ) [Fact p.Prime] :
    Ideal (MvPolynomial (Fin n) (lambdaField n p)) :=
  Ideal.span (Set.range (pthPowerGen n p))

/-- `pthPowerIdeal` is the span of the generators `X i ^ p - C (t i)`. -/
theorem pthPowerIdeal_eq_span (n p : ℕ) [Fact p.Prime] :
    pthPowerIdeal n p = Ideal.span (Set.range (pthPowerGen n p)) :=
  sorry

/-- Each generator `X i ^ p - C (t i)` lies in `pthPowerIdeal`. -/
theorem pthPowerGen_mem (n p : ℕ) [Fact p.Prime] (i : Fin n) :
    pthPowerGen n p i ∈ pthPowerIdeal n p :=
  sorry

/-- The evaluation `X i ↦ x i` vanishes on the generators of `pthPowerIdeal`. -/
theorem aeval_x_pthPowerGen (n p : ℕ) [Fact p.Prime] (i : Fin n) :
    aeval (x n p) (pthPowerGen n p i) = 0 :=
  sorry

/-- The evaluation `X i ↦ x i` vanishes on `pthPowerIdeal`. -/
theorem aeval_eq_zero_of_mem_pthPowerIdeal (n p : ℕ) [Fact p.Prime]
    {f : MvPolynomial (Fin n) (lambdaField n p)} (hf : f ∈ pthPowerIdeal n p) :
    aeval (x n p) f = 0 :=
  sorry

/-- The defining ideal `I = (x_i^p - t_i)` is maximal. -/
instance instIsMaximal_pthPowerIdeal (n p : ℕ) [Fact p.Prime] :
    (pthPowerIdeal n p).IsMaximal :=
  sorry

/-- The `I`-adic completion `Λ[x_1, …, x_n]^∧_I`. -/
abbrev adicCompletion (n p : ℕ) [Fact p.Prime] : Type :=
  AdicCompletion (pthPowerIdeal n p) (MvPolynomial (Fin n) (lambdaField n p))

/-- The completed polynomial ring is local. -/
instance instIsLocalRing_adicCompletion (n p : ℕ) [Fact p.Prime] :
    IsLocalRing (adicCompletion n p) :=
  sorry

/-- The completed polynomial ring is Noetherian. -/
instance instIsNoetherianRing_adicCompletion (n p : ℕ) [Fact p.Prime] :
    IsNoetherianRing (adicCompletion n p) :=
  sorry

/-- The completed polynomial ring is complete local. -/
instance instIsCompleteLocalRing_adicCompletion (n p : ℕ) [Fact p.Prime] :
    IsCompleteLocalRing (adicCompletion n p) :=
  sorry

/-- The carrier of `adicCompletion` is the `I`-adic completion of `Λ[x_1, …, x_n]`. -/
theorem adicCompletion_spec (n p : ℕ) [Fact p.Prime] :
    adicCompletion n p =
      AdicCompletion (pthPowerIdeal n p) (MvPolynomial (Fin n) (lambdaField n p)) :=
  sorry

/-- The residue map of the completion, obtained by evaluating `X i ↦ x i` after
the canonical projection `AdicCompletion I P → P ⧸ I`. -/
def residueHom (n p : ℕ) [Fact p.Prime] :
    adicCompletion n p →ₐ[lambdaField n p] functionField n p :=
  (Ideal.Quotient.liftₐ (pthPowerIdeal n p) (aeval (x n p))
      fun _ hf ↦ aeval_eq_zero_of_mem_pthPowerIdeal n p hf).comp
    ((AdicCompletion.evalOneₐ (pthPowerIdeal n p)).restrictScalars (lambdaField n p))

/-- `residueHom` recovers `aeval (x n p)` on the image of `AdicCompletion.of`. -/
theorem residueHom_of (n p : ℕ) [Fact p.Prime]
    (f : MvPolynomial (Fin n) (lambdaField n p)) :
    residueHom n p
        (algebraMap (MvPolynomial (Fin n) (lambdaField n p)) (adicCompletion n p) f) =
      aeval (x n p) f :=
  sorry

/-- The residue map of the completion is surjective onto `k`. -/
theorem surjective_residueHom (n p : ℕ) [Fact p.Prime] :
    Function.Surjective (residueHom n p) :=
  sorry

/-- The maximal ideal of the completion is the kernel of `residueHom`. -/
theorem maximalIdeal_adicCompletion_eq_ker (n p : ℕ) [Fact p.Prime] :
    maximalIdeal (adicCompletion n p) = RingHom.ker (residueHom n p).toRingHom :=
  sorry

/-- Residue identification of the completion with `k` over `Λ`. -/
def residueFieldIso (n p : ℕ) [Fact p.Prime] :
    ResidueField (adicCompletion n p) ≃ₐ[lambdaField n p] functionField n p :=
  (Ideal.quotientEquivAlgOfEq (lambdaField n p)
      (maximalIdeal_adicCompletion_eq_ker n p)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_residueHom n p))

/-- The residue identification recovers `residueHom` on residue classes. -/
theorem residueFieldIso_apply (n p : ℕ) [Fact p.Prime] (z : adicCompletion n p) :
    residueFieldIso n p (residue (adicCompletion n p) z) = residueHom n p z :=
  sorry

end PurelyInseparable

namespace CompleteLocalAlgCat

/-- The explicit object `R = Λ[x_1, …, x_n]^∧_I` of `Ĉ_Λ`. -/
def pthPowerAdicCompletion (n p : ℕ) [Fact p.Prime] :
    CompleteLocalAlgCat (lambdaField n p) (functionField n p) :=
  of (adicCompletion n p) (PurelyInseparable.residueFieldIso n p)

/-- The carrier of `pthPowerAdicCompletion` is the `I`-adic completion of
`Λ[x_1, …, x_n]`. -/
theorem pthPowerAdicCompletion_carrier (n p : ℕ) [Fact p.Prime] :
    (pthPowerAdicCompletion n p).carrier = adicCompletion n p :=
  sorry

/-- The residue identification of `pthPowerAdicCompletion` is `residueFieldIso`. -/
theorem pthPowerAdicCompletion_residueFieldIso (n p : ℕ) [Fact p.Prime] :
    (pthPowerAdicCompletion n p).residueFieldIso =
      PurelyInseparable.residueFieldIso n p :=
  sorry

end CompleteLocalAlgCat
