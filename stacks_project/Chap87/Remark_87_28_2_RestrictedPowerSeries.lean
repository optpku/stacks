module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.UniformSpace.Pi

/-!
# I-adic restricted power series

If `A` is `I`-adically complete, the restricted power series ring `A{σ}` is the inverse
limit of the discrete polynomial rings `(A ⧸ I ^ n)[σ]`. Mathlib owns that inverse limit as
the `I.map C`-adic completion of `A[σ]`.
-/

@[expose] public section

noncomputable section

universe u v

/-- The `I`-adic restricted power series ring `A{σ}`, realized as the adic completion of
`A[σ]` along the extended coefficient ideal `I · A[σ]`. -/
abbrev IAdicRestrictedPowerSeries {A : Type u} [CommRing A] (σ : Type v) (I : Ideal A) : Type (max u v) :=
  AdicCompletion (I.map (algebraMap A (MvPolynomial σ A))) (MvPolynomial σ A)

namespace IAdicRestrictedPowerSeries

variable {A : Type u} [CommRing A] (σ : Type v) (I : Ideal A)

/-- Unfolding of `IAdicRestrictedPowerSeries` as an adic completion of `A[σ]`. -/
theorem IAdicRestrictedPowerSeries_def :
    IAdicRestrictedPowerSeries σ I =
      AdicCompletion (I.map (algebraMap A (MvPolynomial σ A))) (MvPolynomial σ A) :=
  sorry

/-- The coefficient ideal `I` extended to the `I`-adic completion of `A[σ]`. -/
def extendedIdeal : Ideal (IAdicRestrictedPowerSeries σ I) :=
  Ideal.map (algebraMap (MvPolynomial σ A) (IAdicRestrictedPowerSeries σ I))
    (I.map (algebraMap A (MvPolynomial σ A)))

/-- The extended ideal is the image of `I · A[σ]` under the canonical map into the completion. -/
theorem extendedIdeal_eq_map :
    extendedIdeal σ I =
      Ideal.map (algebraMap (MvPolynomial σ A) (IAdicRestrictedPowerSeries σ I))
        (I.map (algebraMap A (MvPolynomial σ A))) :=
  sorry

/-- The canonical stage map from `A{σ}` to the discrete polynomial ring `(A ⧸ I ^ n)[σ]`. -/
def stageHom (n : ℕ) : IAdicRestrictedPowerSeries σ I →ₐ[A] MvPolynomial σ (A ⧸ I ^ n) :=
  (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm.toAlgHom.comp
    ((Ideal.quotientEquivAlgOfEq A
        (Ideal.map_pow (algebraMap A (MvPolynomial σ A)) I n).symm).toAlgHom.comp
      ((AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial σ A))) n).restrictScalars A))

/-- A polynomial maps to its coefficientwise reduction modulo `I ^ n`. -/
theorem stageHom_map (n : ℕ) (p : MvPolynomial σ A) :
    stageHom σ I n (algebraMap (MvPolynomial σ A) (IAdicRestrictedPowerSeries σ I) p) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p :=
  sorry

/-- Constants map to constant polynomials with coefficients reduced modulo `I ^ n`. -/
theorem stageHom_C (n : ℕ) (a : A) :
    stageHom σ I n (algebraMap A (IAdicRestrictedPowerSeries σ I) a) =
      MvPolynomial.C (Ideal.Quotient.mk (I ^ n) a) :=
  sorry

/-- Indeterminates remain indeterminates in every polynomial stage. -/
theorem stageHom_X (n : ℕ) (i : σ) :
    stageHom σ I n (algebraMap (MvPolynomial σ A) (IAdicRestrictedPowerSeries σ I) (MvPolynomial.X i)) =
      MvPolynomial.X i :=
  sorry

/-- Stage maps are compatible with the inverse system `(A ⧸ I ^ n)[σ]`. -/
theorem stageHom_comp {m n : ℕ} (hmn : m ≤ n) (F : IAdicRestrictedPowerSeries σ I) :
    MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) (stageHom σ I n F) =
      stageHom σ I m F :=
  sorry

/-- A family of polynomial stages is compatible when it is functorial along `I ^ n ⊆ I ^ m`. -/
def CompatibleStages (f : (n : ℕ) → MvPolynomial σ (A ⧸ I ^ n)) : Prop :=
  ∀ ⦃m n : ℕ⦄ (hmn : m ≤ n),
    MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) (f n) = f m

/-- Unfolding of inverse-system compatibility for `I`-adic polynomial stages. -/
theorem compatibleStages_iff (f : (n : ℕ) → MvPolynomial σ (A ⧸ I ^ n)) :
    CompatibleStages σ I f ↔
      ∀ ⦃m n : ℕ⦄ (hmn : m ≤ n),
        MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) (f n) = f m :=
  sorry

/-- Inverse-limit uniformity on `A{σ}`, comapped from the product of discrete uniformities on
the adic stages of `A[σ]`. -/
@[implicit_reducible]
def limitUniformSpace : UniformSpace (IAdicRestrictedPowerSeries σ I) :=
  UniformSpace.comap
    (AdicCompletion.incl (I.map (algebraMap A (MvPolynomial σ A))) (MvPolynomial σ A))
    (@Pi.uniformSpace ℕ
      (fun n ↦
        MvPolynomial σ A ⧸
          ((I.map (algebraMap A (MvPolynomial σ A))) ^ n • ⊤ :
            Ideal (MvPolynomial σ A)))
      (fun _ ↦ ⊥))

/-- Inverse-limit topology on `A{σ}` associated with `limitUniformSpace`. -/
@[implicit_reducible]
def limitTopology : TopologicalSpace (IAdicRestrictedPowerSeries σ I) :=
  (limitUniformSpace σ I).toTopologicalSpace

/-- The limit topology is the topology of the inverse-limit uniformity. -/
theorem limitTopology_eq :
    limitTopology σ I = (limitUniformSpace σ I).toTopologicalSpace :=
  sorry

end IAdicRestrictedPowerSeries
