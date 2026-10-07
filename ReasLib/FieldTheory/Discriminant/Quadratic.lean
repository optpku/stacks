module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
public import ReasLib.FieldTheory.Discriminant
public import ReasLib.FieldTheory.IntermediateField.SimpleExtension

@[expose] public section

open scoped IntermediateField
open Polynomial

universe u v

namespace FieldExtension

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

namespace QuadraticExtension

variable {K L}
variable [Algebra.IsQuadraticExtension K L]

/-- A nonseparable quadratic field extension is purely inseparable and has base-field
characteristic two. -/
theorem isPurelyInseparableAndRingCharEqTwoOfNotSeparable
    (hsep : ¬ Algebra.IsSeparable K L) :
    IsPurelyInseparable K L ∧ ringChar K = 2 := by
  have hmul : Field.finSepDegree K L * Field.finInsepDegree K L = Module.finrank K L :=
    Field.finSepDegree_mul_finInsepDegree (F := K) (E := L)
  have hfinInsep_ne_one : Field.finInsepDegree K L ≠ 1 := by
    simpa [isSeparable_iff_finInsepDegree_eq_one] using hsep
  have hfinInsep_dvd_two : Field.finInsepDegree K L ∣ 2 := by
    refine ⟨Field.finSepDegree K L, ?_⟩
    calc
      2 = Module.finrank K L := by
        symm
        simpa using (Algebra.IsQuadraticExtension.finrank_eq_two K L)
      _ = Field.finSepDegree K L * Field.finInsepDegree K L := hmul.symm
      _ = Field.finInsepDegree K L * Field.finSepDegree K L := by rw [Nat.mul_comm]
  have hfinInsep_eq_two : Field.finInsepDegree K L = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hfinInsep_dvd_two with hdeg | hdeg
    · exact (hfinInsep_ne_one hdeg).elim
    · exact hdeg
  have hfinSep_eq_one : Field.finSepDegree K L = 1 := by
    rw [hfinInsep_eq_two] at hmul
    have hfinrank_two : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
    omega
  have hpure : IsPurelyInseparable K L :=
    isPurelyInseparable_of_finSepDegree_eq_one (F := K) (E := L) hfinSep_eq_one
  refine ⟨hpure, ?_⟩
  obtain ⟨n, hnpow⟩ := finInsepDegree_eq_pow (F := K) (E := L) (q := ringExpChar K)
  have hpow : 2 = ringExpChar K ^ n := by
    rw [hfinInsep_eq_two] at hnpow
    exact hnpow
  rcases expChar_is_prime_or_one K (ringExpChar K) with hprime | hone
  · have hq_dvd_two : ringExpChar K ∣ 2 := by
      cases n with
      | zero => simp at hpow
      | succ m =>
          exact ⟨(ringExpChar K) ^ m, by simpa [pow_succ, Nat.mul_comm] using hpow⟩
    have hq_eq_two : ringExpChar K = 2 :=
      (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).1 hq_dvd_two
    have hExp : ExpChar K 2 := ringExpChar.of_eq (R := K) hq_eq_two
    have htwo_zero : (2 : K) = 0 := by
      cases hExp with
      | prime _ => exact CharP.cast_eq_zero K 2
    exact CharP.ringChar_of_prime_eq_zero (R := K) Nat.prime_two htwo_zero
  · simp [hone] at hpow

/-- The discriminant square class of a nonseparable quadratic field extension is zero. -/
theorem discriminantEqZeroOfNotSeparable
    (hsep : ¬ Algebra.IsSeparable K L) :
    discriminant K L = SquareClassWithZero.mk K 0 := by
  have hdiscr_zero : Algebra.discr K (Module.finBasis K L) = 0 := by
    -- Local instance justification (proof-local temporary data): the quadratic degree makes the trace-matrix index type nonempty for the determinant computation.
    haveI : Nonempty (Fin (Module.finrank K L)) := by
      rw [Algebra.IsQuadraticExtension.finrank_eq_two K L]
      infer_instance
    rw [Algebra.discr_def]
    have hmatrix_zero : Algebra.traceMatrix K (Module.finBasis K L) = 0 := by
      ext i j
      simp [Algebra.traceMatrix_apply, Algebra.trace_eq_zero_of_not_isSeparable hsep]
    simpa [hmatrix_zero] using
      (Matrix.det_zero (n := Fin (Module.finrank K L)) (R := K))
  calc
    discriminant K L = SquareClassWithZero.mk K (Algebra.discr K (Module.finBasis K L)) := by
      simpa using (discriminant_eq (K := K) (L := L) (Module.finBasis K L))
    _ = SquareClassWithZero.mk K 0 := by simp [hdiscr_zero]

/-- A purely inseparable quadratic field extension is not separable. -/
theorem notSeparableOfIsPurelyInseparable
    (hpure : IsPurelyInseparable K L) :
    ¬ Algebra.IsSeparable K L := by
  -- Local instance justification (proof-local temporary data): use the supplied hypothesis with the canonical surjectivity theorem.
  letI : IsPurelyInseparable K L := hpure
  intro hsep
  have htop : (⊥ : IntermediateField K L) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable K L x
    rw [← hy]
    exact IntermediateField.mem_bot.mpr ⟨y, rfl⟩
  have hfinrank_one : Module.finrank K L = 1 :=
    (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).1 htop
  have hfinrank_two : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  omega

/-- A quadratic extension over a field whose characteristic is not two is not purely
inseparable. -/
theorem notPurelyInseparableOfRingCharNeTwo
    (hchar : ringChar K ≠ 2) :
    ¬ IsPurelyInseparable K L := by
  intro hpure
  have hnotsep : ¬ Algebra.IsSeparable K L :=
    notSeparableOfIsPurelyInseparable (K := K) (L := L) hpure
  exact hchar <|
    (isPurelyInseparableAndRingCharEqTwoOfNotSeparable
      (K := K) (L := L) hnotsep).2

/-- A quadratic extension of a field whose characteristic is not two is separable. -/
theorem isSeparableOfRingCharNeTwo
    (hchar : ringChar K ≠ 2) :
    Algebra.IsSeparable K L := by
  by_contra hnot
  exact hchar
    ((isPurelyInseparableAndRingCharEqTwoOfNotSeparable
      (K := K) (L := L) hnot).2)

/-- A primitive generator of a quadratic field extension has a minimal polynomial of degree
two. -/
theorem minpolyNatDegreeEqTwoOfAdjoinSimpleEqTop
    {x : L} (hx_top : K⟮x⟯ = ⊤) :
    (minpoly K x).natDegree = 2 := by
  have hx_int : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hfinrank_simple : Module.finrank K K⟮x⟯ = 2 := by
    calc
      Module.finrank K K⟮x⟯ = Module.finrank K (⊤ : IntermediateField K L) := by
        rw [hx_top]
      _ = Module.finrank K L := by
        simp
      _ = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  rw [IntermediateField.adjoin.finrank hx_int] at hfinrank_simple
  exact hfinrank_simple

/-- A purely inseparable quadratic extension is generated by an element whose square belongs to
the base field. -/
theorem existsSquareGeneratorOfIsPurelyInseparable
    (hpure : IsPurelyInseparable K L) :
    ∃ x : L, x ^ 2 ∈ (⊥ : IntermediateField K L) ∧ K⟮x⟯ = ⊤ := by
  -- Local instance justification (proof-local temporary data): the supplied hypothesis controls the element exponent of the selected generator.
  letI : IsPurelyInseparable K L := hpure
  have hnotsep : ¬ Algebra.IsSeparable K L :=
    notSeparableOfIsPurelyInseparable (K := K) (L := L) hpure
  have hchar : ringChar K = 2 :=
    (isPurelyInseparableAndRingCharEqTwoOfNotSeparable
      (K := K) (L := L) hnotsep).2
  -- Local instance justification (proof-local temporary data): express the established characteristic equation in the form needed by the purely inseparable exponent API.
  haveI : CharP K 2 := ringChar.of_eq hchar
  have hprime : Nat.Prime (Module.finrank K L) := by
    simpa [Algebra.IsQuadraticExtension.finrank_eq_two K L] using Nat.prime_two
  obtain ⟨x, _, hx_adjoin_top⟩ :=
    existsPrimitiveGeneratorOfFinrankPrime (F := K) (E := L) hprime
  have hx_minpoly_degree : (minpoly K x).natDegree = 2 :=
    minpolyNatDegreeEqTwoOfAdjoinSimpleEqTop (K := K) (L := L) hx_adjoin_top
  have hx_elemExponent_one : IsPurelyInseparable.elemExponent K x = 1 := by
    have hpow : 2 ^ IsPurelyInseparable.elemExponent K x = 2 ^ 1 := by
      simpa [hx_minpoly_degree] using
        (IsPurelyInseparable.minpoly_natDegree_eq' (K := K) (L := L) 2 x).symm
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hpow
  have hx_square_range : x ^ 2 ∈ (algebraMap K L).range := by
    refine ⟨IsPurelyInseparable.elemReduct K x, ?_⟩
    simpa [hx_elemExponent_one] using
      (IsPurelyInseparable.algebraMap_elemReduct_eq' (K := K) (L := L) 2 x)
  have hx_square : x ^ 2 ∈ (⊥ : IntermediateField K L) := by
    simpa [IntermediateField.mem_bot] using hx_square_range
  exact ⟨x, hx_square, hx_adjoin_top⟩

/-- A monic polynomial of degree two is determined by its next and constant coefficients. -/
private theorem monicEqXPowTwoAddCMulXAddC {p : K[X]} (hp : p.Monic)
    (hdeg : p.natDegree = 2) :
    p = X ^ 2 + C p.nextCoeff * X + C (p.coeff 0) := by
  have hquad :
      p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    apply Polynomial.eq_quadratic_of_degree_le_two
    exact degree_le_of_natDegree_le (le_of_eq hdeg)
  have hcoeff2 : p.coeff 2 = 1 := by
    simpa [hdeg] using hp.coeff_natDegree
  have hnext : p.nextCoeff = p.coeff 1 := by
    have hpos : 0 < p.natDegree := by
      simpa [hdeg]
    simpa [hdeg] using (Polynomial.nextCoeff_of_natDegree_pos (p := p) hpos)
  calc
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := hquad
    _ = X ^ 2 + C p.nextCoeff * X + C (p.coeff 0) := by
      rw [hcoeff2, ← hnext]
      simp

/-- In a field of ring characteristic two, `-1 = 1`. -/
private theorem negOneEqOneOfRingCharEqTwo (hchar : ringChar K = 2) : (-(1 : K)) = 1 := by
  -- Local instance justification (proof-local temporary data): convert the characteristic equation to the `CharP` interface used for scalar arithmetic.
  letI : CharP K 2 := ringChar.of_eq hchar
  have htwo_zero : (2 : K) = 0 := CharP.cast_eq_zero K 2
  apply add_right_cancel (b := (1 : K))
  simp [one_add_one_eq_two, htwo_zero]

/-- A primitive quadratic generator with trace one in characteristic two has next minimal-polynomial
coefficient one. -/
private theorem minpolyNextCoeffEqOneOfTraceOneCharTwo
    {z : L} (hz_trace : Algebra.trace K L z = 1)
    (hz_top : K⟮z⟯ = ⊤) (hchar : ringChar K = 2) :
    (minpoly K z).nextCoeff = 1 := by
  have hfinrank_z : Module.finrank K⟮z⟯ L = 1 := by
    rw [hz_top]
    simp
  have htrace_formula : Algebra.trace K L z = -(minpoly K z).nextCoeff := by
    simpa [hfinrank_z] using
      (trace_eq_finrank_mul_minpoly_nextCoeff (K := K) (L := L) z)
  have hnext_neg : -(minpoly K z).nextCoeff = 1 := by
    simpa [hz_trace] using htrace_formula.symm
  have hnext_neg_one : (minpoly K z).nextCoeff = -(1 : K) := by
    simpa using congrArg Neg.neg hnext_neg
  simpa [negOneEqOneOfRingCharEqTwo (K := K) hchar] using hnext_neg_one

/-- A primitive quadratic generator with trace zero has next minimal-polynomial coefficient zero. -/
private theorem minpolyNextCoeffEqZeroOfTraceZero
    {y : L} (hy_trace : Algebra.trace K L y = 0) (hy_top : K⟮y⟯ = ⊤) :
    (minpoly K y).nextCoeff = 0 := by
  have hfinrank_y : Module.finrank K⟮y⟯ L = 1 := by
    rw [hy_top]
    simp
  have htrace_formula : Algebra.trace K L y = -(minpoly K y).nextCoeff := by
    simpa [hfinrank_y] using
      (trace_eq_finrank_mul_minpoly_nextCoeff (K := K) (L := L) y)
  have hneg_next : -(minpoly K y).nextCoeff = 0 := by
    simpa [hy_trace] using htrace_formula.symm
  exact neg_eq_zero.mp hneg_next

/-- A separable quadratic extension in characteristic two has a primitive Artin-Schreier generator
of trace one. -/
private theorem existsArtinSchreierGeneratorOfSeparableCharTwo
    (hsep : Algebra.IsSeparable K L) (hchar : ringChar K = 2) :
    ∃ z : L, Algebra.trace K L z = 1 ∧ z ^ 2 - z ∈ (⊥ : IntermediateField K L) ∧
      K⟮z⟯ = ⊤ := by
  -- Local instance justification (proof-local temporary data): translate the source characteristic equality to `CharP` for the Artin-Schreier calculation.
  letI : CharP K 2 := ringChar.of_eq hchar
  -- Local instance justification (proof-local temporary data): transport characteristic two along the injective field map for arithmetic in `L`.
  letI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have htrace_ne_zero : Algebra.trace K L ≠ 0 := by
    -- Local instance justification (proof-local temporary data): expose the supplied separability hypothesis to the trace nonvanishing API.
    letI : Algebra.IsSeparable K L := hsep
    exact Algebra.trace_ne_zero K L
  obtain ⟨x, hx_trace⟩ : ∃ x : L, Algebra.trace K L x ≠ 0 := by
    by_contra hx
    apply htrace_ne_zero
    ext x
    by_cases hx_zero : Algebra.trace K L x = 0
    · exact hx_zero
    · exact False.elim (hx ⟨x, hx_zero⟩)
  let z : L := (algebraMap K L ((Algebra.trace K L x)⁻¹)) * x
  have hz_trace : Algebra.trace K L z = 1 := by
    calc
      Algebra.trace K L z = Algebra.trace K L (((Algebra.trace K L x)⁻¹ : K) • x) := by
        simp [z, Algebra.smul_def]
      _ = (Algebra.trace K L x)⁻¹ * Algebra.trace K L x := by
        simpa [Algebra.smul_def] using
          (LinearMap.map_smul_of_tower (Algebra.trace K L) ((Algebra.trace K L x)⁻¹) x)
      _ = 1 := inv_mul_cancel₀ hx_trace
  have hz_not_bot : z ∉ (⊥ : IntermediateField K L) := by
    intro hz_bot
    rcases IntermediateField.mem_bot.mp hz_bot with ⟨a, ha⟩
    have htwo_zero : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have htrace_bot : Algebra.trace K L z = 0 := by
      calc
        Algebra.trace K L z = (2 : K) * a := by
          rw [ha.symm, Algebra.trace_algebraMap]
          simp [Algebra.IsQuadraticExtension.finrank_eq_two K L]
        _ = 0 := by simp [htwo_zero]
    have hzero_one : (0 : K) = 1 := htrace_bot.symm.trans hz_trace
    exact zero_ne_one hzero_one
  have hprime : Nat.Prime (Module.finrank K L) := by
    simpa [Algebra.IsQuadraticExtension.finrank_eq_two K L] using Nat.prime_two
  have hz_top : K⟮z⟯ = ⊤ :=
    adjoinSimpleEqTopOfNotMemBotOfFinrankPrime (F := K) (E := L) hprime hz_not_bot
  have hz_int : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hdeg : (minpoly K z).natDegree = 2 :=
    minpolyNatDegreeEqTwoOfAdjoinSimpleEqTop (K := K) (L := L) hz_top
  have hnext_one : (minpoly K z).nextCoeff = 1 :=
    minpolyNextCoeffEqOneOfTraceOneCharTwo (K := K) (L := L) hz_trace hz_top hchar
  have hpoly :
      minpoly K z =
        X ^ 2 + C (minpoly K z).nextCoeff * X + C ((minpoly K z).coeff 0) :=
    monicEqXPowTwoAddCMulXAddC (K := K)
      (p := minpoly K z) (minpoly.monic hz_int) hdeg
  have hz_root :
      z ^ 2 + z + algebraMap K L ((minpoly K z).coeff 0) = 0 := by
    have hroot := minpoly.aeval K z
    rw [hpoly] at hroot
    simpa [hnext_one] using hroot
  have hneg_z : -z = z := by
    have htwo_zero : (2 : L) = 0 := CharP.cast_eq_zero L 2
    apply neg_eq_iff_add_eq_zero.mpr
    calc
      z + z = (2 : L) * z := by ring
      _ = 0 := by simp [htwo_zero]
  have hz_as : z ^ 2 - z = algebraMap K L (-(minpoly K z).coeff 0) := by
    calc
      z ^ 2 - z = z ^ 2 + z := by simp [sub_eq_add_neg, hneg_z]
      _ = algebraMap K L (-(minpoly K z).coeff 0) := by
        calc
          z ^ 2 + z = z ^ 2 + z + algebraMap K L ((minpoly K z).coeff 0) -
              algebraMap K L ((minpoly K z).coeff 0) := by ring
          _ = algebraMap K L (-(minpoly K z).coeff 0) := by
              rw [hz_root]
              simp
  have hz_as_bot : z ^ 2 - z ∈ (⊥ : IntermediateField K L) := by
    exact IntermediateField.mem_bot.mpr ⟨-(minpoly K z).coeff 0, hz_as.symm⟩
  exact ⟨z, hz_trace, hz_as_bot, hz_top⟩

/-- A trace-one primitive generator of a quadratic extension in characteristic two has
discriminant square class one. -/
private theorem discriminantEqOneOfTraceOneGeneratorCharTwo
    (hsep : Algebra.IsSeparable K L) {z : L} (hz_trace : Algebra.trace K L z = 1)
    (hz_top : K⟮z⟯ = ⊤)
    (hchar : ringChar K = 2) :
    discriminant K L = SquareClassWithZero.mk K 1 := by
  -- Local instance justification (proof-local temporary data): expose the supplied separability hypothesis to the power-basis discriminant formula.
  letI : Algebra.IsSeparable K L := hsep
  -- Local instance justification (proof-local temporary data): convert the characteristic equation to the `CharP` interface used for the derivative calculation.
  letI : CharP K 2 := ringChar.of_eq hchar
  -- Local instance justification (proof-local temporary data): transport characteristic two to the extension field for arithmetic on the generator.
  letI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hz_int : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hdeg : (minpoly K z).natDegree = 2 :=
    minpolyNatDegreeEqTwoOfAdjoinSimpleEqTop (K := K) (L := L) hz_top
  have hnext_one : (minpoly K z).nextCoeff = 1 :=
    minpolyNextCoeffEqOneOfTraceOneCharTwo (K := K) (L := L) hz_trace hz_top hchar
  have hpoly :
      minpoly K z =
        X ^ 2 + C (minpoly K z).nextCoeff * X + C ((minpoly K z).coeff 0) :=
    monicEqXPowTwoAddCMulXAddC (K := K)
      (p := minpoly K z) (minpoly.monic hz_int) hdeg
  have hz_deriv : Polynomial.aeval z (minpoly K z).derivative = 1 := by
    have htwo_zero : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hone_add : (1 : K) + 1 = 0 := by
      simpa [one_add_one_eq_two] using htwo_zero
    have hderiv : (minpoly K z).derivative = (1 : K[X]) := by
      rw [hpoly]
      simp [hnext_one, hone_add]
    rw [hderiv]
    simp
  have hz_top_subalg : Algebra.adjoin K ({z} : Set L) = ⊤ := by
    simpa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (F := K) (E := L) (hα := (isAlgebraic_iff_isIntegral.2 hz_int))] using
      congrArg IntermediateField.toSubalgebra hz_top
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hz_int hz_top_subalg
  have hpb_gen : pb.gen = z := by
    simpa [pb] using (PowerBasis.ofAdjoinEqTop_gen (K := K) (S := L) hz_int hz_top_subalg)
  have hdiscr : Algebra.discr K pb.basis = 1 := by
    calc
      Algebra.discr K pb.basis =
          (-1) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2) *
            Algebra.norm K (Polynomial.aeval pb.gen (minpoly K pb.gen).derivative) := by
              simpa using (Algebra.discr_powerBasis_eq_norm (K := K) (L := L) (pb := pb))
      _ = (-1 : K) ^ 1 * Algebra.norm K (1 : L) := by
            simp [Algebra.IsQuadraticExtension.finrank_eq_two K L, hpb_gen, hz_deriv]
      _ = 1 := by
            simp [negOneEqOneOfRingCharEqTwo (K := K) hchar]
  calc
    discriminant K L = SquareClassWithZero.mk K (Algebra.discr K pb.basis) := by
      simpa using (discriminant_eq (K := K) (L := L) pb.basis)
    _ = SquareClassWithZero.mk K 1 := by rw [hdiscr]

/-- A separable quadratic extension in characteristic two has discriminant square class one. -/
theorem discriminantEqOneOfIsSeparableAndRingCharEqTwo
    (hsep : Algebra.IsSeparable K L) (hchar : ringChar K = 2) :
    discriminant K L = SquareClassWithZero.mk K 1 := by
  obtain ⟨z, hz_trace, _, hz_top⟩ :=
    existsArtinSchreierGeneratorOfSeparableCharTwo (K := K) (L := L) hsep hchar
  exact discriminantEqOneOfTraceOneGeneratorCharTwo
    (K := K) (L := L) hsep hz_trace hz_top hchar

/-- A quadratic extension in characteristic different from two has a primitive trace-zero
generator whose square belongs to the base field. -/
theorem existsTraceZeroSquareGeneratorOfRingCharNeTwo
    (hchar : ringChar K ≠ 2) :
    ∃ y : L, Algebra.trace K L y = 0 ∧ y ^ 2 ∈ (⊥ : IntermediateField K L) ∧
      K⟮y⟯ = ⊤ := by
  have htwo_ne_zero : (2 : K) ≠ 0 := by
    intro htwo_zero
    exact hchar (CharP.ringChar_of_prime_eq_zero (R := K) Nat.prime_two htwo_zero)
  have hprime : Nat.Prime (Module.finrank K L) := by
    simpa [Algebra.IsQuadraticExtension.finrank_eq_two K L] using Nat.prime_two
  obtain ⟨x, hx_not_bot, hx_top⟩ :=
    existsPrimitiveGeneratorOfFinrankPrime (F := K) (E := L) hprime
  let t : K := (2 : K)⁻¹ * Algebra.trace K L x
  let y : L := x - algebraMap K L t
  have hy_trace : Algebra.trace K L y = 0 := by
    calc
      Algebra.trace K L y = Algebra.trace K L x - Algebra.trace K L (algebraMap K L t) := by
        simp [y]
      _ = Algebra.trace K L x - (2 : K) * t := by
        rw [Algebra.trace_algebraMap]
        simp [Algebra.IsQuadraticExtension.finrank_eq_two K L]
      _ = Algebra.trace K L x - (2 : K) * ((2 : K)⁻¹ * Algebra.trace K L x) := by
        simp [t]
      _ = 0 := by
        rw [show (2 : K) * ((2 : K)⁻¹ * Algebra.trace K L x) =
            ((2 : K) * (2 : K)⁻¹) * Algebra.trace K L x by ring]
        rw [mul_inv_cancel₀ htwo_ne_zero, one_mul, sub_self]
  have hy_not_bot : y ∉ (⊥ : IntermediateField K L) := by
    intro hy_bot
    have ht_mem : algebraMap K L t ∈ (⊥ : IntermediateField K L) :=
      IntermediateField.mem_bot.mpr ⟨t, rfl⟩
    have hx_mem : x ∈ (⊥ : IntermediateField K L) := by
      have hx_eq : x = y + algebraMap K L t := by simp [y]
      rw [hx_eq]
      exact (⊥ : IntermediateField K L).add_mem hy_bot ht_mem
    exact hx_not_bot hx_mem
  have hy_top : K⟮y⟯ = ⊤ :=
    adjoinSimpleEqTopOfNotMemBotOfFinrankPrime (F := K) (E := L) hprime hy_not_bot
  have hy_int : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hdeg : (minpoly K y).natDegree = 2 :=
    minpolyNatDegreeEqTwoOfAdjoinSimpleEqTop (K := K) (L := L) hy_top
  have hnext_zero : (minpoly K y).nextCoeff = 0 :=
    minpolyNextCoeffEqZeroOfTraceZero (K := K) (L := L) hy_trace hy_top
  have hpoly :
      minpoly K y =
        X ^ 2 + C (minpoly K y).nextCoeff * X + C ((minpoly K y).coeff 0) :=
    monicEqXPowTwoAddCMulXAddC (K := K)
      (p := minpoly K y) (minpoly.monic hy_int) hdeg
  have hy_root : y ^ 2 + algebraMap K L ((minpoly K y).coeff 0) = 0 := by
    have hroot := minpoly.aeval K y
    rw [hpoly] at hroot
    simpa [hnext_zero] using hroot
  have hy_square_eq : y ^ 2 = algebraMap K L (-(minpoly K y).coeff 0) := by
    calc
      y ^ 2 = y ^ 2 + algebraMap K L ((minpoly K y).coeff 0) -
          algebraMap K L ((minpoly K y).coeff 0) := by ring
      _ = algebraMap K L (-(minpoly K y).coeff 0) := by
          rw [hy_root]
          simp
  have hy_square_bot : y ^ 2 ∈ (⊥ : IntermediateField K L) := by
    exact IntermediateField.mem_bot.mpr ⟨-(minpoly K y).coeff 0, hy_square_eq.symm⟩
  exact ⟨y, hy_trace, hy_square_bot, hy_top⟩

/-- A primitive trace-zero square-root generator represents the discriminant square class of a
quadratic extension in characteristic different from two. -/
private theorem discriminantEqMkOfTraceZeroSquareGenerator
    {y : L} (hy_trace : Algebra.trace K L y = 0) {a : K}
    (hy : y ^ 2 = algebraMap K L a) (hy_top : K⟮y⟯ = ⊤) (hchar : ringChar K ≠ 2) :
    discriminant K L = SquareClassWithZero.mk K a := by
  have hsep : Algebra.IsSeparable K L :=
    isSeparableOfRingCharNeTwo (K := K) (L := L) hchar
  -- Local instance justification (proof-local temporary data): expose the derived separability fact to the power-basis discriminant formula.
  letI : Algebra.IsSeparable K L := hsep
  have htwo_ne_zero : (2 : K) ≠ 0 := by
    intro htwo_zero
    exact hchar (CharP.ringChar_of_prime_eq_zero (R := K) Nat.prime_two htwo_zero)
  have hy_int : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hdeg : (minpoly K y).natDegree = 2 :=
    minpolyNatDegreeEqTwoOfAdjoinSimpleEqTop (K := K) (L := L) hy_top
  have hnext_zero : (minpoly K y).nextCoeff = 0 :=
    minpolyNextCoeffEqZeroOfTraceZero (K := K) (L := L) hy_trace hy_top
  have hpoly :
      minpoly K y =
        X ^ 2 + C (minpoly K y).nextCoeff * X + C ((minpoly K y).coeff 0) :=
    monicEqXPowTwoAddCMulXAddC (K := K)
      (p := minpoly K y) (minpoly.monic hy_int) hdeg
  have hy_root : y ^ 2 + algebraMap K L ((minpoly K y).coeff 0) = 0 := by
    have hroot := minpoly.aeval K y
    rw [hpoly] at hroot
    simpa [hnext_zero] using hroot
  have hy_square_eq : y ^ 2 = algebraMap K L (-(minpoly K y).coeff 0) := by
    calc
      y ^ 2 = y ^ 2 + algebraMap K L ((minpoly K y).coeff 0) -
          algebraMap K L ((minpoly K y).coeff 0) := by ring
      _ = algebraMap K L (-(minpoly K y).coeff 0) := by
          rw [hy_root]
          simp
  have hcoeff0_neg : -(minpoly K y).coeff 0 = a := by
    exact (algebraMap K L).injective (hy_square_eq.symm.trans hy)
  have hcoeff0 : (minpoly K y).coeff 0 = -a := by
    simpa using congrArg Neg.neg hcoeff0_neg
  have hy_top_subalg : Algebra.adjoin K ({y} : Set L) = ⊤ := by
    simpa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (F := K) (E := L)
      (hα := (isAlgebraic_iff_isIntegral.2 (Algebra.IsIntegral.isIntegral y)))] using
      congrArg IntermediateField.toSubalgebra hy_top
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hy_int hy_top_subalg
  have hpb_gen : pb.gen = y := by
    simpa [pb] using (PowerBasis.ofAdjoinEqTop_gen (K := K) (S := L) hy_int hy_top_subalg)
  have hpb_dim : pb.dim = 2 := by
    simpa [pb, hdeg] using (PowerBasis.ofAdjoinEqTop_dim (K := K) (S := L) hy_int hy_top_subalg)
  have hy_deriv : Polynomial.aeval y (minpoly K y).derivative = (2 : L) * y := by
    have hderiv : (minpoly K y).derivative = C (2 : K) * X := by
      rw [hpoly]
      simpa [hnext_zero, one_add_one_eq_two, C_eq_natCast]
    rw [hderiv]
    calc
      Polynomial.aeval y (C (2 : K) * X) = algebraMap K L (2 : K) * y := by simp
      _ = (2 : L) * y := by
          rw [show algebraMap K L (2 : K) = (2 : L) from map_natCast (algebraMap K L) 2]
  have hnorm_y : Algebra.norm K y = -a := by
    calc
      Algebra.norm K y = Algebra.norm K pb.gen := by simp [hpb_gen]
      _ = (-1 : K) ^ pb.dim * (minpoly K pb.gen).coeff 0 := by
          simpa using (Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb)
      _ = -a := by simp [hpb_dim, hpb_gen, hcoeff0]
  have hy_deriv_norm :
      Algebra.norm K (Polynomial.aeval y (minpoly K y).derivative) = -4 * a := by
    calc
      Algebra.norm K (Polynomial.aeval y (minpoly K y).derivative) =
          Algebra.norm K ((2 : L) * y) := by rw [hy_deriv]
      _ = Algebra.norm K (algebraMap K L (2 : K) * y) := by
          rw [show (2 : L) = algebraMap K L (2 : K) from
            (map_natCast (algebraMap K L) 2).symm]
      _ = Algebra.norm K (algebraMap K L (2 : K)) * Algebra.norm K y := by rw [map_mul]
      _ = (2 : K) ^ 2 * (-a) := by
          rw [hnorm_y, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two K L]
      _ = -4 * a := by ring
  have hdiscr : Algebra.discr K pb.basis = 4 * a := by
    calc
      Algebra.discr K pb.basis =
          (-1) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2) *
            Algebra.norm K (Polynomial.aeval pb.gen (minpoly K pb.gen).derivative) := by
              simpa using (Algebra.discr_powerBasis_eq_norm (K := K) (L := L) (pb := pb))
      _ = (-1 : K) * (-4 * a) := by
            simp [Algebra.IsQuadraticExtension.finrank_eq_two K L, hpb_gen, hy_deriv_norm]
      _ = 4 * a := by ring
  have hsquare : SquareClassWithZero.mk K (4 * a) = SquareClassWithZero.mk K a := by
    rw [SquareClassWithZero.mk_eq_mk_iff]
    refine ⟨Units.mk0 2 htwo_ne_zero, ?_⟩
    simp only [Units.val_mk0, pow_two]
    ring
  calc
    discriminant K L = SquareClassWithZero.mk K (Algebra.discr K pb.basis) := by
      simpa using (discriminant_eq (K := K) (L := L) pb.basis)
    _ = SquareClassWithZero.mk K (4 * a) := by rw [hdiscr]
    _ = SquareClassWithZero.mk K a := hsquare

/-- A primitive square-root generator represents the discriminant square class of a quadratic
extension in characteristic different from two. -/
theorem discriminantEqMkOfSquareGenerator
    {y : L} {a : K} (hy : y ^ 2 = algebraMap K L a) (hy_top : K⟮y⟯ = ⊤)
    (hchar : ringChar K ≠ 2) :
    discriminant K L = SquareClassWithZero.mk K a := by
  let q : K[X] := X ^ 2 - C a
  have hy_int : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hq_monic : q.Monic := by
    simpa [q] using (Polynomial.monic_X_pow_sub_C a (by norm_num : (2 : ℕ) ≠ 0))
  have hq_root : Polynomial.aeval y q = 0 := by
    simp [q, hy]
  have hmin_dvd : minpoly K y ∣ q := minpoly.dvd K y hq_root
  have hdeg : (minpoly K y).natDegree = 2 :=
    minpolyNatDegreeEqTwoOfAdjoinSimpleEqTop (K := K) (L := L) hy_top
  have hq_eq_minpoly : q = minpoly K y := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hy_int) hq_monic hmin_dvd
    simp [q, hdeg]
  have hfinrank_y : Module.finrank K⟮y⟯ L = 1 := by
    rw [hy_top]
    simp
  have hq_nextCoeff : q.nextCoeff = 0 := by
    have hq_pos : 0 < q.natDegree := by
      simp [q]
    rw [Polynomial.nextCoeff_of_natDegree_pos (p := q) hq_pos]
    simp [q]
  have hy_trace : Algebra.trace K L y = 0 := by
    calc
      Algebra.trace K L y = Module.finrank K⟮y⟯ L * -(minpoly K y).nextCoeff := by
        simpa using (trace_eq_finrank_mul_minpoly_nextCoeff (K := K) (L := L) y)
      _ = 0 := by
        rw [hfinrank_y, ← hq_eq_minpoly, hq_nextCoeff]
        simp
  exact discriminantEqMkOfTraceZeroSquareGenerator
    (K := K) (L := L) hy_trace hy hy_top hchar

/-- In characteristic different from two, a quadratic extension is generated by a square root
whose base-field square class is its discriminant. -/
theorem existsDiscriminantSquareRootGeneratorOfRingCharNeTwo
    (hchar : ringChar K ≠ 2) :
    ∃ y : L, ∃ a : K, discriminant K L = SquareClassWithZero.mk K a ∧
      y ^ 2 = algebraMap K L a ∧ K⟮y⟯ = ⊤ := by
  obtain ⟨y, _, hy_square_bot, hy_top⟩ :=
    existsTraceZeroSquareGeneratorOfRingCharNeTwo (K := K) (L := L) hchar
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hy_square_bot
  have hy : y ^ 2 = algebraMap K L a := by
    simpa using ha.symm
  have hdisc : discriminant K L = SquareClassWithZero.mk K a :=
    discriminantEqMkOfSquareGenerator
      (K := K) (L := L) hy hy_top hchar
  exact ⟨y, a, hdisc, hy, hy_top⟩

/-- In characteristic different from two, the discriminant square class of a quadratic extension
is not the square class of one. -/
theorem discriminantNeOneOfRingCharNeTwo
    (hchar : ringChar K ≠ 2) :
    discriminant K L ≠ SquareClassWithZero.mk K 1 := by
  intro hdiscr_one
  obtain ⟨y, a, hdiscr, hy, hy_top⟩ :=
    existsDiscriminantSquareRootGeneratorOfRingCharNeTwo (K := K) (L := L) hchar
  have hsq : SquareClassWithZero.mk K a = SquareClassWithZero.mk K 1 := by
    calc
      SquareClassWithZero.mk K a = discriminant K L := hdiscr.symm
      _ = SquareClassWithZero.mk K 1 := hdiscr_one
  rcases (SquareClassWithZero.mk_eq_mk_iff (K := K) (a := a) (b := (1 : K))).1 hsq with
    ⟨u, hu⟩
  have hu_sq : a = (↑u : K) ^ 2 := by
    simpa [pow_two] using hu
  have hfactor :
      (y - algebraMap K L (↑u : K)) * (y + algebraMap K L (↑u : K)) = 0 := by
    calc
      (y - algebraMap K L (↑u : K)) * (y + algebraMap K L (↑u : K)) =
          y ^ 2 - (algebraMap K L (↑u : K)) ^ 2 := by ring
      _ = algebraMap K L a - algebraMap K L ((↑u : K) ^ 2) := by
          rw [hy, map_pow]
      _ = 0 := by
          rw [hu_sq]
          ring
  have hy_bot : y ∈ (⊥ : IntermediateField K L) := by
    rcases mul_eq_zero.mp hfactor with hy_minus | hy_plus
    · exact IntermediateField.mem_bot.mpr ⟨(↑u : K), (sub_eq_zero.mp hy_minus).symm⟩
    · have hy_eq : y = algebraMap K L (-(↑u : K)) := by
        calc
          y = y + algebraMap K L (↑u : K) - algebraMap K L (↑u : K) := by ring
          _ = algebraMap K L (-(↑u : K)) := by
              rw [hy_plus]
              simp
      exact IntermediateField.mem_bot.mpr ⟨-(↑u : K), hy_eq.symm⟩
  have hy_adjoin_bot : K⟮y⟯ = (⊥ : IntermediateField K L) :=
    (IntermediateField.adjoin_simple_eq_bot_iff).2 hy_bot
  have hbot_top : (⊥ : IntermediateField K L) = ⊤ := hy_adjoin_bot.symm.trans hy_top
  have hfinrank_one : Module.finrank K L = 1 :=
    (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).1 hbot_top
  have hfinrank_two : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  omega

end QuadraticExtension

end FieldExtension
