module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Prime
public import Mathlib.Topology.LocallyFinite

/-!
# Weil divisors

A Weil divisor is a locally finite integer linear combination of prime divisors.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

section

variable (X : Scheme.{u})

/-- A Weil divisor is a formal integer linear combination of prime divisors whose
nonzero-coefficient support is locally finite. -/
def WeilDivisor : Type u :=
  { coeff : PrimeDivisor X → ℤ //
    LocallyFinite fun Z : PrimeDivisor X ↦
      if coeff Z = 0 then (∅ : Set X) else (Z.support : Set X) }

/-- Construct a Weil divisor from an integer coefficient function whose nonzero support family is
locally finite. -/
def WeilDivisor.ofCoeff (coeff : PrimeDivisor X → ℤ)
    (locallyFinite_support :
      LocallyFinite fun Z : PrimeDivisor X ↦
        if coeff Z = 0 then (∅ : Set X) else (Z.support : Set X)) :
    WeilDivisor X :=
  ⟨coeff, locallyFinite_support⟩

/-- The integer coefficient of a prime divisor in a Weil divisor. -/
abbrev WeilDivisor.coeff {Y : Scheme.{u}} (D : WeilDivisor Y) : PrimeDivisor Y → ℤ :=
  D.1

/-- The family attached to a Weil divisor, supported on those prime divisors with nonzero
coefficient. -/
abbrev WeilDivisor.supportFamily {Y : Scheme.{u}}
    (D : WeilDivisor Y) : PrimeDivisor Y → Set Y := fun Z ↦
  if D.coeff Z = 0 then (∅ : Set Y) else (Z.support : Set Y)

/-- The nonzero-coefficient support family of a Weil divisor is locally finite. -/
theorem WeilDivisor.locallyFinite_supportFamily {Y : Scheme.{u}} (D : WeilDivisor Y) :
    LocallyFinite D.supportFamily :=
  D.2

private theorem locallyFinite_nonzeroCoefficients_add (D E : WeilDivisor X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if D.coeff Z + E.coeff Z = 0 then (∅ : Set X) else (Z.support : Set X) := by
  let f := D.supportFamily
  let g := E.supportFamily
  have hf : LocallyFinite f := D.locallyFinite_supportFamily
  have hg : LocallyFinite g := E.locallyFinite_supportFamily
  have hfg : LocallyFinite fun Z ↦ f Z ∪ g Z := by
    intro x
    rcases hf x with ⟨s, hs, hfs⟩
    rcases hg x with ⟨t, ht, hgt⟩
    refine ⟨s ∩ t, Filter.inter_mem hs ht, ?_⟩
    refine (hfs.union hgt).subset ?_
    intro Z hZ
    rcases hZ with ⟨y, hy⟩
    rcases hy with ⟨hyfg, hst⟩
    rcases hyfg with hyf | hyg
    · left
      exact ⟨y, hyf, hst.1⟩
    · right
      exact ⟨y, hyg, hst.2⟩
  refine hfg.subset ?_
  intro Z x hx
  by_cases hsum : D.coeff Z + E.coeff Z = 0
  · simp [hsum] at hx
  · have hx' : x ∈ (Z.support : Set X) := by
      simpa [hsum] using hx
    by_cases hD : D.coeff Z = 0
    · have hE : E.coeff Z ≠ 0 := by
        intro hE
        exact hsum (by simp [hD, hE])
      exact Or.inr <| by simpa [g, hE] using hx'
    · exact Or.inl <| by simpa [f, hD] using hx'

private theorem locallyFinite_nonzeroCoefficients_neg (D : WeilDivisor X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if -D.coeff Z = 0 then (∅ : Set X) else (Z.support : Set X) := by
  simp_rw [neg_eq_zero]
  change LocallyFinite D.supportFamily
  exact D.locallyFinite_supportFamily

/-- Two Weil divisors with equal coefficients are equal. -/
@[ext]
theorem WeilDivisor.ext {D E : WeilDivisor X}
    (hcoeff : ∀ Z : PrimeDivisor X, D.coeff Z = E.coeff Z) : D = E := by
  exact Subtype.ext (funext hcoeff)

/-- The zero Weil divisor has all coefficients equal to `0`. -/
instance instZeroWeilDivisor : Zero (WeilDivisor X) where
  zero :=
    WeilDivisor.ofCoeff X (fun _ ↦ 0) <| by
      intro x
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      simp

/-- Addition of Weil divisors is defined coefficientwise. -/
instance instAddWeilDivisor : Add (WeilDivisor X) where
  add D E :=
    WeilDivisor.ofCoeff X (fun Z ↦ D.coeff Z + E.coeff Z) <| by
      simpa using locallyFinite_nonzeroCoefficients_add X D E

/-- Negation of Weil divisors is defined coefficientwise. -/
instance instNegWeilDivisor : Neg (WeilDivisor X) where
  neg D :=
    WeilDivisor.ofCoeff X (fun Z ↦ -D.coeff Z) <| by
      simpa using locallyFinite_nonzeroCoefficients_neg X D

/-- Subtraction of Weil divisors is defined coefficientwise. -/
instance instSubWeilDivisor : Sub (WeilDivisor X) where
  sub D E :=
    WeilDivisor.ofCoeff X (fun Z ↦ D.coeff Z - E.coeff Z) <| by
      have h := locallyFinite_nonzeroCoefficients_add X D (-E)
      change LocallyFinite fun Z ↦
        if D.coeff Z + -E.coeff Z = 0 then (∅ : Set X) else (Z.support : Set X) at h
      simpa only [sub_eq_add_neg] using h

/-- Every coefficient of the zero Weil divisor is zero. -/
@[simp] theorem WeilDivisor.coeff_zero (Z : PrimeDivisor X) : (0 : WeilDivisor X).coeff Z = 0 := rfl

/-- The coefficient of a sum of Weil divisors is the sum of their coefficients. -/
@[simp] theorem WeilDivisor.coeff_add (D E : WeilDivisor X) (Z : PrimeDivisor X) :
    (D + E).coeff Z = D.coeff Z + E.coeff Z := rfl

/-- The coefficient of the negation of a Weil divisor is the negation of its coefficient. -/
@[simp] theorem WeilDivisor.coeff_neg (D : WeilDivisor X) (Z : PrimeDivisor X) :
    (-D).coeff Z = -D.coeff Z := rfl

/-- The coefficient of a difference of Weil divisors is the difference of their coefficients. -/
@[simp] theorem WeilDivisor.coeff_sub (D E : WeilDivisor X) (Z : PrimeDivisor X) :
    (D - E).coeff Z = D.coeff Z - E.coeff Z := rfl

/-- Natural-number scalar multiplication of Weil divisors is repeated addition. -/
instance instSMulNatWeilDivisor : SMul ℕ (WeilDivisor X) where
  smul := nsmulRec

/-- Integer scalar multiplication of Weil divisors is repeated addition and subtraction. -/
instance instSMulIntWeilDivisor : SMul ℤ (WeilDivisor X) where
  smul := zsmulRec

/-- Natural-number scalar multiplication acts coefficientwise on Weil divisors. -/
@[simp] theorem WeilDivisor.coeff_nsmul (n : ℕ) (D : WeilDivisor X) (Z : PrimeDivisor X) :
    (n • D).coeff Z = n • D.coeff Z := by
  change (nsmulRec n D).coeff Z = _
  induction n with
  | zero =>
    simp only [nsmulRec.eq_def, WeilDivisor.coeff_zero, zero_nsmul]
  | succ n ih =>
    rw [nsmulRec.eq_def, WeilDivisor.coeff_add, ih, succ_nsmul]

/-- Integer scalar multiplication acts coefficientwise on Weil divisors. -/
@[simp] theorem WeilDivisor.coeff_zsmul (n : ℤ) (D : WeilDivisor X) (Z : PrimeDivisor X) :
    (n • D).coeff Z = n • D.coeff Z := by
  cases n with
  | ofNat n =>
    change (nsmulRec n D).coeff Z = _
    exact WeilDivisor.coeff_nsmul X n D Z
  | negSucc n =>
    change -(nsmulRec n.succ D).coeff Z = _
    rw [negSucc_zsmul]
    congr 1
    exact WeilDivisor.coeff_nsmul X n.succ D Z

/-- Weil divisors are determined by their coefficient functions. -/
theorem WeilDivisor.coeff_injective : Function.Injective (fun D : WeilDivisor X ↦ D.coeff) := by
  intro D E h
  ext Z
  exact congrFun h Z

/-- Weil divisors form an additive commutative group under pointwise operations on coefficients. -/
instance instAddCommGroupWeilDivisor : AddCommGroup (WeilDivisor X) :=
  Function.Injective.addCommGroup
    (fun D : WeilDivisor X ↦ D.coeff) (WeilDivisor.coeff_injective X)
    rfl
    (fun _ _ ↦ rfl)
    (fun _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun D n ↦ funext <| WeilDivisor.coeff_nsmul X n D)
    (fun D n ↦ funext <| WeilDivisor.coeff_zsmul X n D)

notation "Div(" X ")" => WeilDivisor X

end

end AlgebraicGeometry
