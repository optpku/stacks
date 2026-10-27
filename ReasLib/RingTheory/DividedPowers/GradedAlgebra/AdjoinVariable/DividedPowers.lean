/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.AdjoinVariable.Bundled

/-!
# Divided powers on algebras obtained by adjoining one variable

This file identifies the even and positive-even parts of the bundled odd- and even-variable
extensions with their coefficient models.  The reindexing maps are explicit finite-support
sums.  They transport the coefficient formulas to canonical divided-power structures without
choosing a witness from an existence theorem.
-/

@[expose] public section

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u v

namespace NonnegGradedAlgebra.Adjoin

variable {R : Type u} [CommRing R]

private theorem castPiece_add (A : NonnegGradedAlgebra.{u, v} R)
    {m n : ℕ} (h : m = n) (x y : A.piece m) :
    cast (congrArg A.piece h) (x + y) =
      cast (congrArg A.piece h) x + cast (congrArg A.piece h) y := by
  cases h
  rfl

private theorem castPiece_smul (A : NonnegGradedAlgebra.{u, v} R)
    {m n : ℕ} (h : m = n) (r : R) (x : A.piece m) :
    cast (congrArg A.piece h) (r • x) = r • cast (congrArg A.piece h) x := by
  cases h
  rfl

private theorem castPiece_zero (A : NonnegGradedAlgebra.{u, v} R)
    {m n : ℕ} (h : m = n) : cast (congrArg A.piece h) 0 = 0 := by
  cases h
  rfl

private theorem sum_add_of_add {ι : Type*} {β : ι → Type*}
    [∀ i, AddCommMonoid (β i)] {M : Type*} [AddCommMonoid M]
    (f : ∀ i, β i → M) (hzero : ∀ i, f i 0 = 0)
    (hadd : ∀ i x y, f i (x + y) = f i x + f i y) (x y : Π₀ i, β i) :
    Implementation.sum (x + y) f = Implementation.sum x f + Implementation.sum y f := by
  letI : DecidableEq ι := Classical.decEq ι
  letI : ∀ i (x : β i), Decidable (x ≠ 0) := fun _ x ↦ Classical.propDecidable (x ≠ 0)
  exact DFinsupp.sum_add_index hzero hadd

private theorem sum_smul_of_linear {ι : Type*} {β : ι → Type*}
    [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (f : ∀ i, β i → M) (hzero : ∀ i, f i 0 = 0)
    (hsmul : ∀ i (r : R) (x : β i), f i (r • x) = r • f i x) (r : R) (x : Π₀ i, β i) :
    Implementation.sum (r • x) f = r • Implementation.sum x f := by
  letI : DecidableEq ι := Classical.decEq ι
  letI : ∀ i (x : β i), Decidable (x ≠ 0) := fun _ x ↦ Classical.propDecidable (x ≠ 0)
  unfold Implementation.sum
  change (DFinsupp.mapRange (fun _ xi ↦ r • xi) (fun _ ↦ smul_zero r) x).sum f = _
  rw [DFinsupp.sum_mapRange_index hzero, DFinsupp.smul_sum]
  congr 1
  funext i xi
  exact hsmul i r xi

namespace Odd

variable (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ)

/-- Reindex one homogeneous coefficient of an even-degree odd-variable piece into the parity
coefficient model. -/
def evenCoeffTerm (hd : Odd d) (k : ℕ)
    (i : {i : Fin 2 // (i : ℕ) * d ≤ 2 * k})
    (x : A.piece (2 * k - (i : ℕ) * d)) : Coeffs A :=
  if hi : (i : ℕ) = 0 then
    (A.evenHom k <| cast (congrArg A.piece <|
      (congrArg (fun q : ℕ ↦ 2 * k - q * d) hi).trans <|
        (congrArg (fun q : ℕ ↦ 2 * k - q) (Nat.zero_mul d)).trans <|
          Nat.sub_zero (2 * k)) x, 0)
  else
    (0, A.oddHom ((2 * k - d) / 2) <| cast (congrArg A.piece <|
      ((congrArg (fun q : Fin 2 ↦ 2 * k - (q : ℕ) * d)
        (Fin.eq_one_of_ne_zero i.1 fun h ↦ hi (congrArg Fin.val h))).trans <|
          congrArg (fun q : ℕ ↦ 2 * k - q) (Nat.one_mul d)).trans <|
        (Nat.two_mul_div_two_add_one_of_odd <|
          Nat.Even.sub_odd
            (Eq.mp (congrArg (fun q : ℕ ↦ q ≤ 2 * k) <|
              (congrArg (fun q : ℕ ↦ q * d) (congrArg Fin.val <|
                Fin.eq_one_of_ne_zero i.1 fun h ↦ hi (congrArg Fin.val h))).trans <|
                  Nat.one_mul d) i.property)
            (even_two_mul k) hd).symm) x)

private theorem oddCoeffDegree (hd : Odd d) (k : ℕ)
    (i : {i : Fin 2 // (i : ℕ) * d ≤ 2 * k}) (hi : (i : ℕ) ≠ 0) :
    2 * k - (i : ℕ) * d = 2 * ((2 * k - d) / 2) + 1 := by
  have hiOne : (i : ℕ) = 1 := congrArg Fin.val <|
    Fin.eq_one_of_ne_zero i.1 (fun h ↦ hi (congrArg Fin.val h))
  have hdle : d ≤ 2 * k := by simpa only [hiOne, Nat.one_mul] using i.property
  simpa only [hiOne, Nat.one_mul] using
    (Nat.two_mul_div_two_add_one_of_odd (Nat.Even.sub_odd hdle (even_two_mul k) hd)).symm

private theorem evenCoeffTerm_zero (hd : Odd d) (k : ℕ)
    (i : {i : Fin 2 // (i : ℕ) * d ≤ 2 * k}) :
    evenCoeffTerm A d hd k i 0 = 0 := by
  unfold evenCoeffTerm
  split_ifs with hi
  · have hdeg : 2 * k - (i : ℕ) * d = 2 * k := by simp [hi]
    simp [castPiece_zero A hdeg, map_zero]
  · simp [castPiece_zero A (oddCoeffDegree d hd k i hi), map_zero]

private theorem evenCoeffTerm_add (hd : Odd d) (k : ℕ)
    (i : {i : Fin 2 // (i : ℕ) * d ≤ 2 * k}) (x y : A.piece (2 * k - (i : ℕ) * d)) :
    evenCoeffTerm A d hd k i (x + y) =
      evenCoeffTerm A d hd k i x + evenCoeffTerm A d hd k i y := by
  unfold evenCoeffTerm
  split_ifs with hi
  · have hdeg : 2 * k - (i : ℕ) * d = 2 * k := by simp [hi]
    simp [castPiece_add A hdeg, map_add]
  · simp [castPiece_add A (oddCoeffDegree d hd k i hi), map_add]

private theorem evenCoeffTerm_smul (hd : Odd d) (k : ℕ)
    (i : {i : Fin 2 // (i : ℕ) * d ≤ 2 * k}) (r : R) (x : A.piece (2 * k - (i : ℕ) * d)) :
    evenCoeffTerm A d hd k i (r • x) = r • evenCoeffTerm A d hd k i x := by
  unfold evenCoeffTerm
  split_ifs with hi
  · have hdeg : 2 * k - (i : ℕ) * d = 2 * k := by simp [hi]
    simp [castPiece_smul A hdeg, map_smul]
  · simp [castPiece_smul A (oddCoeffDegree d hd k i hi), map_smul]

/-- Reindex an even element of the odd-variable extension into its two parity coefficients. -/
def evenToCoeffsFun (hd : Odd d) (z : (algebra A d hd).evenPart) : Coeffs A :=
  Implementation.sum z fun k x ↦
    Implementation.sum x fun i xi ↦ evenCoeffTerm A d hd k i xi

/-- Reindexing even odd-variable coefficients preserves addition. -/
theorem evenToCoeffsFun_add (hd : Odd d) (x y : (algebra A d hd).evenPart) :
    evenToCoeffsFun A d hd (x + y) = evenToCoeffsFun A d hd x + evenToCoeffsFun A d hd y := by
  unfold evenToCoeffsFun
  apply sum_add_of_add
  · intro k
    rfl
  · intro k x y
    exact sum_add_of_add (evenCoeffTerm A d hd k)
      (evenCoeffTerm_zero A d hd k) (evenCoeffTerm_add A d hd k) x y

/-- Reindexing even odd-variable coefficients preserves scalar multiplication. -/
theorem evenToCoeffsFun_smul (hd : Odd d) (r : R) (x : (algebra A d hd).evenPart) :
    evenToCoeffsFun A d hd (r • x) = r • evenToCoeffsFun A d hd x := by
  unfold evenToCoeffsFun
  apply sum_smul_of_linear
  · intro k
    rfl
  · intro k r x
    exact sum_smul_of_linear (evenCoeffTerm A d hd k)
      (evenCoeffTerm_zero A d hd k) (evenCoeffTerm_smul A d hd k) r x

/-- The linear parity reindexing from the even part of an odd-variable extension. -/
def evenToCoeffs (hd : Odd d) : (algebra A d hd).evenPart →ₗ[R] Coeffs A where
  toFun := evenToCoeffsFun A d hd
  map_add' := evenToCoeffsFun_add A d hd
  map_smul' := evenToCoeffsFun_smul A d hd

/-- Insert an odd homogeneous base coefficient as the coefficient of the adjoined variable. -/
def oddCoeffFun (j : ℕ) (x : A.piece (2 * j + 1)) : Piece A d (2 * j + 1 + d) :=
  DFinsupp.single
    ⟨(1 : Fin 2),
      Eq.mp (congrArg (fun q : ℕ ↦ q ≤ 2 * j + 1 + d) (Nat.one_mul d).symm) <|
        Nat.le_add_left d (2 * j + 1)⟩
    (cast (congrArg A.piece <|
      ((Nat.add_sub_cancel_right (2 * j + 1) d).symm.trans <|
        congrArg (fun q : ℕ ↦ 2 * j + 1 + d - q) (Nat.one_mul d).symm)) x)

/-- Insertion of odd coefficients into an odd-variable extension preserves addition. -/
theorem oddCoeffFun_add (j : ℕ)
    (x y : A.piece (2 * j + 1)) :
    oddCoeffFun A d j (x + y) = oddCoeffFun A d j x + oddCoeffFun A d j y := by
  unfold oddCoeffFun
  rw [castPiece_add A (by simp)]
  exact DFinsupp.single_add _ _ _

/-- Insertion of odd coefficients into an odd-variable extension preserves scalar multiplication. -/
theorem oddCoeffFun_smul (j : ℕ) (r : R)
    (x : A.piece (2 * j + 1)) :
    oddCoeffFun A d j (r • x) = r • oddCoeffFun A d j x := by
  unfold oddCoeffFun
  rw [castPiece_smul A (by simp)]
  exact DFinsupp.single_smul _ _

/-- The linear insertion of an odd base coefficient as the variable coefficient. -/
def oddCoeffMap (j : ℕ) : A.piece (2 * j + 1) →ₗ[R] Piece A d (2 * j + 1 + d) where
  toFun := oddCoeffFun A d j
  map_add' := oddCoeffFun_add A d j
  map_smul' := oddCoeffFun_smul A d j

/-- Insert an odd homogeneous base coefficient times the adjoined variable into the even part. -/
def oddCoeffHom (hd : Odd d) (j : ℕ) :
    A.piece (2 * j + 1) →ₗ[R] (algebra A d hd).evenPart :=
  ((algebra A d hd).evenHom ((2 * j + 1 + d) / 2)).comp <|
    ((algebra A d hd).pieceCast <|
      (Nat.two_mul_div_two_of_even ((odd_two_mul_add_one j).add_odd hd)).symm).comp <|
        oddCoeffMap A d j

/-- Insert parity coefficients into the even part of an odd-variable extension. -/
def evenOfCoeffs (hd : Odd d) : Coeffs A →ₗ[R] (algebra A d hd).evenPart :=
  (DirectSum.toModule R ℕ (algebra A d hd).evenPart fun k ↦
      ((algebra A d hd).evenHom k).comp (baseMap A d (2 * k))).comp
        (LinearMap.fst R A.evenPart A.oddPart) +
    (DirectSum.toModule R ℕ (algebra A d hd).evenPart fun j ↦ oddCoeffHom A d hd j).comp
      (LinearMap.snd R A.evenPart A.oddPart)

/-- The two explicit parity reindexings for the even part of an odd-variable extension are
mutually inverse. -/
theorem evenOfCoeffs_evenToCoeffs (hd : Odd d) (x : (algebra A d hd).evenPart) :
    evenOfCoeffs A d hd (evenToCoeffs A d hd x) = x := sorry

/-- Reindexing after inserting odd-variable parity coefficients is the identity. -/
theorem evenToCoeffs_evenOfCoeffs (hd : Odd d) (x : Coeffs A) :
    evenToCoeffs A d hd (evenOfCoeffs A d hd x) = x := sorry

/-- The even part of an odd-variable extension is linearly equivalent to an even base
coefficient together with an odd coefficient of the variable. -/
@[stacks 09PH "odd-variable even-part reindexing"]
def evenReindex (hd : Odd d) : (algebra A d hd).evenPart ≃ₗ[R] Coeffs A where
  toLinearMap := evenToCoeffs A d hd
  invFun := evenOfCoeffs A d hd
  left_inv := evenOfCoeffs_evenToCoeffs A d hd
  right_inv := evenToCoeffs_evenOfCoeffs A d hd

/-- Forget positivity in the odd-variable parity coefficient model. -/
def positiveCoeffsToCoeffs : PositiveCoeffs A →ₗ[R] Coeffs A :=
  (A.evenPositiveToEven.comp (LinearMap.fst R A.evenPositivePart A.oddPart)).prod
    (LinearMap.snd R A.evenPositivePart A.oddPart)

/-- Project an odd-variable parity coefficient family onto its positive-even coefficient model. -/
def coeffsToPositive : Coeffs A →ₗ[R] PositiveCoeffs A :=
  (A.evenToEvenPositive.comp (LinearMap.fst R A.evenPart A.oddPart)).prod
    (LinearMap.snd R A.evenPart A.oddPart)

/-- The explicit forward reindexing on the positive-even part of an odd-variable extension. -/
def positiveToCoeffs (hd : Odd d) :
    (algebra A d hd).evenPositivePart →ₗ[R] PositiveCoeffs A :=
  (coeffsToPositive A).comp <| (evenToCoeffs A d hd).comp (algebra A d hd).evenPositiveToEven

/-- The explicit inverse reindexing on positive odd-variable parity coefficients. -/
def positiveOfCoeffs (hd : Odd d) :
    PositiveCoeffs A →ₗ[R] (algebra A d hd).evenPositivePart :=
  (algebra A d hd).evenToEvenPositive.comp <|
    (evenOfCoeffs A d hd).comp (positiveCoeffsToCoeffs A)

/-- The positive-even odd-variable coefficient reindexings are mutually inverse. -/
theorem positiveOfCoeffs_positiveToCoeffs (hd : Odd d)
    (x : (algebra A d hd).evenPositivePart) :
    positiveOfCoeffs A d hd (positiveToCoeffs A d hd x) = x := sorry

/-- Reindexing after inserting positive odd-variable coefficients is the identity. -/
theorem positiveToCoeffs_positiveOfCoeffs (hd : Odd d) (x : PositiveCoeffs A) :
    positiveToCoeffs A d hd (positiveOfCoeffs A d hd x) = x := sorry

/-- The positive-even part of an odd-variable extension is the positive parity coefficient model. -/
@[stacks 09PH "odd-variable positive-even reindexing"]
def positiveReindex (hd : Odd d) :
    (algebra A d hd).evenPositivePart ≃ₗ[R] PositiveCoeffs A where
  toLinearMap := positiveToCoeffs A d hd
  invFun := positiveOfCoeffs A d hd
  left_inv := positiveOfCoeffs_positiveToCoeffs A d hd
  right_inv := positiveToCoeffs_positiveOfCoeffs A d hd

/-- Positive odd-variable coefficient divided powers, with the positive base coefficient retained
as explicit positive-even data. -/
def positiveGammaCoeffs (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (n : ℕ+) (x : PositiveCoeffs A) : PositiveCoeffs A :=
  (gammaA.gammaPos n x.1, A.evenMulOdd (gammaA ((n : ℕ) - 1) x.1) x.2)

/-- The transported total divided-power family on the odd-variable extension. -/
def extensionGamma (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ) (x : (algebra A d hd).evenPositivePart) : (algebra A d hd).evenPart :=
  evenOfCoeffs A d hd <| gamma A gammaA n (positiveToCoeffs A d hd x)

/-- The transported positive-index divided powers on the odd-variable extension. -/
def extensionGammaPos (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ+) (x : (algebra A d hd).evenPositivePart) :
    (algebra A d hd).evenPositivePart :=
  positiveOfCoeffs A d hd <| positiveGammaCoeffs A gammaA n (positiveToCoeffs A d hd x)

/-- In coefficient coordinates, the transported odd-variable operation is the explicit
coefficient formula. -/
@[simp]
theorem evenToCoeffs_extensionGamma
    (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ) (x : (algebra A d hd).evenPositivePart) :
    evenToCoeffs A d hd (extensionGamma A d gammaA hd n x) =
      gamma A gammaA n (positiveToCoeffs A d hd x) := by
  exact evenToCoeffs_evenOfCoeffs A d hd _

/-- Positive coefficient coordinates expose the positive-index odd-variable formula. -/
@[simp]
theorem positiveToCoeffs_extensionGammaPos
    (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ+) (x : (algebra A d hd).evenPositivePart) :
    positiveToCoeffs A d hd (extensionGammaPos A d gammaA hd n x) =
      positiveGammaCoeffs A gammaA n (positiveToCoeffs A d hd x) := by
  exact positiveToCoeffs_positiveOfCoeffs A d hd _

/-- The transported total and positive-index odd-variable operations agree after inclusion. -/
theorem extensionGamma_eq_extensionGammaPos
    (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ+) (x : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd n x =
      (algebra A d hd).evenPositiveToEven (extensionGammaPos A d gammaA hd n x) := sorry

/-- Transported odd-variable divided powers have the expected homogeneous degree. -/
theorem extensionGamma_degree (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n q : ℕ) (x : (algebra A d hd).piece (2 * (q + 1))) :
    ∃ y : (algebra A d hd).piece (2 * (n * (q + 1))),
      extensionGamma A d gammaA hd n ((algebra A d hd).evenPositiveHom q x) =
        (algebra A d hd).evenHom (n * (q + 1)) y := sorry

/-- The first transported odd-variable divided power is positive-even inclusion. -/
theorem extensionGamma_one (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (x : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd 1 x = (algebra A d hd).evenPositiveToEven x := sorry

/-- The zeroth transported odd-variable divided power is the graded unit. -/
theorem extensionGamma_zero (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (x : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd 0 x = (algebra A d hd).oneEven := by
  unfold extensionGamma gamma ofEven evenOfCoeffs
  simp [NonnegGradedAlgebra.oneEven, baseMap, baseCoeff, zeroIndex]
  rfl

/-- Transported odd-variable divided powers obey the binomial multiplication law. -/
theorem extensionGamma_mul (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n m : ℕ) (x : (algebra A d hd).evenPositivePart) :
    (algebra A d hd).evenMul (extensionGamma A d gammaA hd n x)
        (extensionGamma A d gammaA hd m x) =
      Nat.choose (n + m) n • extensionGamma A d gammaA hd (n + m) x := sorry

/-- Transported odd-variable divided powers are compatible with even multiplication. -/
theorem extensionGamma_evenMul (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ) (x : (algebra A d hd).evenPart)
    (y : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd n ((algebra A d hd).evenMulPositive x y) =
      (algebra A d hd).evenMul ((algebra A d hd).evenPow x n)
        (extensionGamma A d gammaA hd n y) := sorry

/-- Higher transported odd-variable divided powers vanish on products of odd homogeneous terms. -/
theorem extensionGamma_oddMul (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    {n : ℕ} (hn : 1 < n) (i j : ℕ)
    (x : (algebra A d hd).piece (2 * i + 1))
    (y : (algebra A d hd).piece (2 * j + 1)) :
    extensionGamma A d gammaA hd n ((algebra A d hd).oddMulTerm i j x y) = 0 := sorry

/-- Transported odd-variable divided powers send sums to antidiagonal convolution. -/
theorem extensionGamma_add (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ) (x y : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd n (x + y) =
      (Finset.antidiagonal n).sum fun ij ↦
        (algebra A d hd).evenMul (extensionGamma A d gammaA hd ij.1 x)
          (extensionGamma A d gammaA hd ij.2 y) := sorry

/-- Iterated transported odd-variable divided powers use `Nat.uniformBell`. -/
theorem extensionGamma_comp (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ) (m : ℕ+) (x : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd n (extensionGammaPos A d gammaA hd m x) =
      Nat.uniformBell n m • extensionGamma A d gammaA hd (n * (m : ℕ)) x := sorry

/-- Example 23.6.2 (Adjoining odd variable) (Tag 09PH): the canonical divided powers on the
bundled algebra obtained by adjoining one variable of odd degree. -/
@[stacks 09PH "canonical odd-variable divided powers"]
def dividedPowers (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d) :
    NonnegGradedAlgebra.DividedPowers (algebra A d hd) where
  gamma := extensionGamma A d gammaA hd
  gammaPos := extensionGammaPos A d gammaA hd
  gamma_eq_gammaPos := extensionGamma_eq_extensionGammaPos A d gammaA hd
  gamma_degree := extensionGamma_degree A d gammaA hd
  gamma_one := extensionGamma_one A d gammaA hd
  gamma_zero := extensionGamma_zero A d gammaA hd
  gamma_mul := extensionGamma_mul A d gammaA hd
  gamma_evenMul := extensionGamma_evenMul A d gammaA hd
  gamma_oddMul := extensionGamma_oddMul A d gammaA hd
  gamma_add := extensionGamma_add A d gammaA hd
  gamma_comp := extensionGamma_comp A d gammaA hd

/-- Evaluation of the canonical odd-variable divided powers is the transported explicit formula. -/
@[simp]
theorem dividedPowers_apply (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ) (x : (algebra A d hd).evenPositivePart) :
    dividedPowers A d gammaA hd n x = extensionGamma A d gammaA hd n x := by
  rfl

/-- The positive component of the canonical odd-variable divided powers is explicit. -/
@[simp]
theorem dividedPowers_gammaPos (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ+) (x : (algebra A d hd).evenPositivePart) :
    (dividedPowers A d gammaA hd).gammaPos n x = extensionGammaPos A d gammaA hd n x := by
  rfl

/-- The coefficient coordinates of a candidate divided-power operation on the odd-variable
extension. -/
def gammaCoords (hd : Odd d) (delta : NonnegGradedAlgebra.DividedPowers (algebra A d hd))
    (n : ℕ) (z : PositiveCoeffs A) : Coeffs A :=
  evenToCoeffs A d hd (delta n (positiveOfCoeffs A d hd z))

/-- A divided-power structure on the odd-variable extension is canonical when its coefficient
coordinates satisfy the textbook recursion and its restriction to the base is `gammaA`. -/
structure IsCanonical (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (delta : NonnegGradedAlgebra.DividedPowers (algebra A d hd)) : Prop where
  /-- The zeroth operation is the constant unit coefficient. -/
  zero (z : PositiveCoeffs A) : gammaCoords A d hd delta 0 z = ofEven A A.oneEven
  /-- Positive operations satisfy
  `gamma (n + 1) (x + yT) = gammaA (n + 1) x + gammaA n x * yT`. -/
  succ (n : ℕ) (x : A.evenPositivePart) (y : A.oddPart) :
    gammaCoords A d hd delta (n + 1) (x, y) =
      (gammaA (n + 1) x, A.evenMulOdd (gammaA n x) y)
  /-- The candidate divided powers restrict to the prescribed divided powers on the base. -/
  base (n : ℕ) (x : A.evenPositivePart) :
    delta n ((inclusion A d hd).evenPositiveMap x) =
      (inclusion A d hd).evenMap (gammaA n x)

/-- The explicit odd-variable divided powers satisfy the canonical coefficient recursion and
base restriction. -/
theorem dividedPowers_isCanonical (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d) :
    IsCanonical A d gammaA hd (dividedPowers A d gammaA hd) := sorry

/-- Any odd-variable divided-power structure satisfying the canonical coefficient recursion is
the explicit transported structure. -/
theorem IsCanonical.eq_dividedPowers (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    {delta : NonnegGradedAlgebra.DividedPowers (algebra A d hd)}
    (hdelta : IsCanonical A d gammaA hd delta) :
    delta = dividedPowers A d gammaA hd := by
  have hcoords (n : ℕ) (z : PositiveCoeffs A) :
      gammaCoords A d hd delta n z = gamma A gammaA n z := by
    cases n with
    | zero => exact hdelta.zero z
    | succ n => exact hdelta.succ n z.1 z.2
  apply NonnegGradedAlgebra.DividedPowers.ext
  intro n x
  apply (evenReindex A d hd).injective
  have h := hcoords n (positiveToCoeffs A d hd x)
  dsimp only [gammaCoords] at h
  rw [positiveOfCoeffs_positiveToCoeffs] at h
  exact h.trans (evenToCoeffs_extensionGamma A d gammaA hd n x).symm

/-- The uniqueness clause of Example 23.6.2 (Adjoining odd variable) (Tag 09PH): the explicit
transported divided powers are the unique canonical structure on the bundled extension. -/
@[stacks 09PH "unique canonical odd-variable divided powers"]
theorem existsUnique_dividedPowers
    (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d) :
    ∃! delta : NonnegGradedAlgebra.DividedPowers (algebra A d hd),
      IsCanonical A d gammaA hd delta := by
  refine ⟨dividedPowers A d gammaA hd, dividedPowers_isCanonical A d gammaA hd, ?_⟩
  intro delta hdelta
  exact hdelta.eq_dividedPowers A d gammaA hd

/-- The odd-variable extension bundled as a divided-power graded algebra. -/
@[stacks 09PH "bundled odd-variable divided-power algebra"]
def dpAlgebra (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d) :
    DividedPowerGradedAlgebra.{u, v} R :=
  DividedPowerGradedAlgebra.of (algebra A d hd) (dividedPowers A d gammaA hd)

/-- The base inclusion into an odd-variable extension preserves the transported divided powers. -/
theorem inclusion_map_gamma (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    (n : ℕ) (x : A.evenPositivePart) :
    (inclusion A d hd).evenMap (gammaA n x) =
      dividedPowers A d gammaA hd n ((inclusion A d hd).evenPositiveMap x) := by
  exact (dividedPowers_isCanonical A d gammaA hd).base n x |>.symm

/-- The canonical inclusion into an odd-variable extension as a divided-power morphism. -/
def inclusionDP (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d) :
    NonnegGradedAlgebra.DividedPowers.Hom gammaA (dividedPowers A d gammaA hd) where
  toGradedHom := inclusion A d hd
  map_gamma := inclusion_map_gamma A d gammaA hd

/-- Forgetting divided powers from the canonical odd-variable inclusion recovers `inclusion`. -/
@[simp]
theorem inclusionDP_toGradedHom (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d) :
    (inclusionDP A d gammaA hd).toGradedHom = inclusion A d hd := by
  rfl

/-- An odd-variable lift from a divided-power base map preserves the canonical transported
divided powers. -/
theorem lift_map_gamma (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (z : B.piece d)
    (n : ℕ) (x : (algebra A d hd).evenPositivePart) :
    (lift A d hd g.toGradedHom z).evenMap (dividedPowers A d gammaA hd n x) =
      gammaB n ((lift A d hd g.toGradedHom z).evenPositiveMap x) := sorry

/-- The canonical divided-power lift out of an odd-variable extension. -/
def liftDP (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (z : B.piece d) :
    NonnegGradedAlgebra.DividedPowers.Hom (dividedPowers A d gammaA hd) gammaB where
  toGradedHom := lift A d hd g.toGradedHom z
  map_gamma := lift_map_gamma A d gammaA hd gammaB g z

/-- Forgetting divided powers from the canonical odd-variable lift recovers the graded lift. -/
@[simp]
theorem liftDP_toGradedHom (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (z : B.piece d) :
    (liftDP A d gammaA hd gammaB g z).toGradedHom = lift A d hd g.toGradedHom z := by
  rfl

/-- The odd-variable divided-power lift restricts to its prescribed base morphism. -/
@[simp]
theorem inclusionDP_comp_liftDP (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (z : B.piece d) :
    NonnegGradedAlgebra.DividedPowers.Hom.comp (liftDP A d gammaA hd gammaB g z)
      (inclusionDP A d gammaA hd) = g := by
  apply NonnegGradedAlgebra.DividedPowers.Hom.ext_toGradedHom
  exact lift_base A d hd g.toGradedHom z

/-- The odd-variable divided-power lift sends the adjoined generator to the prescribed element. -/
@[simp]
theorem liftDP_generator (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (z : B.piece d) :
    (liftDP A d gammaA hd gammaB g z).toGradedHom.map d (generator A d) = z := by
  exact lift_generator A d hd g.toGradedHom z

/-- A divided-power morphism out of the odd-variable extension is determined by its base
restriction and generator value. -/
theorem liftDP_unique (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Odd d)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (z : B.piece d)
    (f : NonnegGradedAlgebra.DividedPowers.Hom (dividedPowers A d gammaA hd) gammaB)
    (hbase : NonnegGradedAlgebra.DividedPowers.Hom.comp f (inclusionDP A d gammaA hd) = g)
    (hgenerator : f.toGradedHom.map d (generator A d) = z) :
    f = liftDP A d gammaA hd gammaB g z := by
  apply NonnegGradedAlgebra.DividedPowers.Hom.ext_toGradedHom
  apply lift_unique A d hd g.toGradedHom z f.toGradedHom
  constructor
  · show inclusion A d hd ≫ f.toGradedHom = g.toGradedHom
    exact congrArg NonnegGradedAlgebra.DividedPowers.Hom.toGradedHom hbase
  · exact hgenerator

end Odd

namespace Even

variable (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ)

/-- Reindex one homogeneous coefficient of an even-degree even-variable piece by its divided
monomial exponent. -/
def evenCoeffTerm (hd : Even d) (k : ℕ)
    (i : {i : ℕ // i * d ≤ 2 * k}) (x : A.piece (2 * k - i * d)) : Coeffs A :=
  Finsupp.single i <| A.evenHom ((2 * k - i * d) / 2) <|
    cast (congrArg A.piece <| (Nat.two_mul_div_two_of_even <|
      (Nat.even_sub i.property).mpr <|
        Iff.intro (fun _ ↦ hd.mul_left i) (fun _ ↦ even_two_mul k)).symm) x

private theorem evenCoeffTerm_zero (hd : Even d) (k : ℕ)
    (i : {i : ℕ // i * d ≤ 2 * k}) :
    evenCoeffTerm A d hd k i 0 = 0 := by
  have hdeg : 2 * k - i * d = 2 * ((2 * k - i * d) / 2) :=
    (Nat.two_mul_div_two_of_even <| (Nat.even_sub i.property).mpr
      ⟨fun _ ↦ hd.mul_left i, fun _ ↦ even_two_mul k⟩).symm
  simp [evenCoeffTerm, castPiece_zero A hdeg, Finsupp.single_zero]

private theorem evenCoeffTerm_add (hd : Even d) (k : ℕ)
    (i : {i : ℕ // i * d ≤ 2 * k}) (x y : A.piece (2 * k - i * d)) :
    evenCoeffTerm A d hd k i (x + y) =
      evenCoeffTerm A d hd k i x + evenCoeffTerm A d hd k i y := by
  have hdeg : 2 * k - i * d = 2 * ((2 * k - i * d) / 2) :=
    (Nat.two_mul_div_two_of_even <| (Nat.even_sub i.property).mpr
      ⟨fun _ ↦ hd.mul_left i, fun _ ↦ even_two_mul k⟩).symm
  simp [evenCoeffTerm, castPiece_add A hdeg, Finsupp.single_add]

private theorem evenCoeffTerm_smul (hd : Even d) (k : ℕ)
    (i : {i : ℕ // i * d ≤ 2 * k}) (r : R) (x : A.piece (2 * k - i * d)) :
    evenCoeffTerm A d hd k i (r • x) = r • evenCoeffTerm A d hd k i x := by
  have hdeg : 2 * k - i * d = 2 * ((2 * k - i * d) / 2) :=
    (Nat.two_mul_div_two_of_even <| (Nat.even_sub i.property).mpr
      ⟨fun _ ↦ hd.mul_left i, fun _ ↦ even_two_mul k⟩).symm
  simp [evenCoeffTerm, castPiece_smul A hdeg, Finsupp.single_smul]

/-- Reindex an even element of the even-variable extension into divided-monomial coefficients. -/
def evenToCoeffsFun (hd : Even d) (z : (algebra A d hd).evenPart) : Coeffs A :=
  Implementation.sum z fun k x ↦
    Implementation.sum x fun i xi ↦ evenCoeffTerm A d hd k i xi

/-- Reindexing even even-variable coefficients preserves addition. -/
theorem evenToCoeffsFun_add (hd : Even d) (x y : (algebra A d hd).evenPart) :
    evenToCoeffsFun A d hd (x + y) = evenToCoeffsFun A d hd x + evenToCoeffsFun A d hd y := by
  unfold evenToCoeffsFun
  apply sum_add_of_add
  · intro k
    rfl
  · intro k x y
    exact sum_add_of_add (evenCoeffTerm A d hd k)
      (evenCoeffTerm_zero A d hd k) (evenCoeffTerm_add A d hd k) x y

/-- Reindexing even even-variable coefficients preserves scalar multiplication. -/
theorem evenToCoeffsFun_smul (hd : Even d) (r : R) (x : (algebra A d hd).evenPart) :
    evenToCoeffsFun A d hd (r • x) = r • evenToCoeffsFun A d hd x := by
  unfold evenToCoeffsFun
  apply sum_smul_of_linear
  · intro k
    rfl
  · intro k r x
    exact sum_smul_of_linear (evenCoeffTerm A d hd k)
      (evenCoeffTerm_zero A d hd k) (evenCoeffTerm_smul A d hd k) r x

/-- The linear coefficient reindexing from the even part of an even-variable extension. -/
def evenToCoeffs (hd : Even d) : (algebra A d hd).evenPart →ₗ[R] Coeffs A where
  toFun := evenToCoeffsFun A d hd
  map_add' := evenToCoeffsFun_add A d hd
  map_smul' := evenToCoeffsFun_smul A d hd

/-- Insert an even homogeneous base coefficient at a specified divided-monomial exponent. -/
def evenCoeffFun (i j : ℕ) (x : A.piece (2 * j)) : Piece A d (2 * j + i * d) :=
  DFinsupp.single ⟨i, Nat.le_add_left (i * d) (2 * j)⟩
    (cast (congrArg A.piece (Nat.add_sub_cancel_right (2 * j) (i * d)).symm) x)

/-- Insertion at a fixed divided-monomial exponent preserves addition. -/
theorem evenCoeffFun_add (i j : ℕ) (x y : A.piece (2 * j)) :
    evenCoeffFun A d i j (x + y) = evenCoeffFun A d i j x + evenCoeffFun A d i j y := by
  simp [evenCoeffFun, castPiece_add, DFinsupp.single_add]

/-- Insertion at a fixed divided-monomial exponent preserves scalar multiplication. -/
theorem evenCoeffFun_smul (i j : ℕ) (r : R) (x : A.piece (2 * j)) :
    evenCoeffFun A d i j (r • x) = r • evenCoeffFun A d i j x := by
  simp [evenCoeffFun, castPiece_smul, DFinsupp.single_smul]

/-- The linear insertion at a fixed divided-monomial exponent. -/
def evenCoeffMap (i j : ℕ) : A.piece (2 * j) →ₗ[R] Piece A d (2 * j + i * d) where
  toFun := evenCoeffFun A d i j
  map_add' := evenCoeffFun_add A d i j
  map_smul' := evenCoeffFun_smul A d i j

/-- Insert one even homogeneous coefficient into the even part of the extension. -/
def evenCoeffHom (hd : Even d) (i j : ℕ) :
    A.piece (2 * j) →ₗ[R] (algebra A d hd).evenPart :=
  ((algebra A d hd).evenHom ((2 * j + i * d) / 2)).comp <|
    ((algebra A d hd).pieceCast <|
      (Nat.two_mul_div_two_of_even ((even_two_mul j).add (hd.mul_left i))).symm).comp <|
        evenCoeffMap A d i j

/-- Insert a full even base coefficient at one divided-monomial exponent. -/
def evenFamilyHom (hd : Even d) (i : ℕ) :
    A.evenPart →ₗ[R] (algebra A d hd).evenPart :=
  DirectSum.toModule R ℕ (algebra A d hd).evenPart fun j ↦ evenCoeffHom A d hd i j

/-- Insert all divided-monomial coefficient families into the even part of the extension. -/
def evenOfCoeffsFun (hd : Even d) (x : Coeffs A) : (algebra A d hd).evenPart :=
  x.sum fun i xi ↦ evenFamilyHom A d hd i xi

/-- Inserting even-variable coefficient families preserves addition. -/
theorem evenOfCoeffsFun_add (hd : Even d) (x y : Coeffs A) :
    evenOfCoeffsFun A d hd (x + y) = evenOfCoeffsFun A d hd x + evenOfCoeffsFun A d hd y := by
  exact (Finsupp.lsum R (evenFamilyHom A d hd)).map_add x y

/-- Inserting even-variable coefficient families preserves scalar multiplication. -/
theorem evenOfCoeffsFun_smul (hd : Even d) (r : R) (x : Coeffs A) :
    evenOfCoeffsFun A d hd (r • x) = r • evenOfCoeffsFun A d hd x := by
  exact (Finsupp.lsum R (evenFamilyHom A d hd)).map_smul r x

/-- The linear insertion of divided-monomial coefficient families. -/
def evenOfCoeffs (hd : Even d) : Coeffs A →ₗ[R] (algebra A d hd).evenPart where
  toFun := evenOfCoeffsFun A d hd
  map_add' := evenOfCoeffsFun_add A d hd
  map_smul' := evenOfCoeffsFun_smul A d hd

/-- The explicit divided-monomial reindexings of the even part are mutually inverse. -/
theorem evenOfCoeffs_evenToCoeffs (hd : Even d) (x : (algebra A d hd).evenPart) :
    evenOfCoeffs A d hd (evenToCoeffs A d hd x) = x := sorry

/-- Reindexing after inserting divided-monomial coefficients is the identity. -/
theorem evenToCoeffs_evenOfCoeffs (hd : Even d) (x : Coeffs A) :
    evenToCoeffs A d hd (evenOfCoeffs A d hd x) = x := sorry

/-- The even part of an even-variable extension is the finitely supported family of its
divided-monomial coefficients. -/
@[stacks 09PI "even-variable even-part reindexing"]
def evenReindex (hd : Even d) : (algebra A d hd).evenPart ≃ₗ[R] Coeffs A where
  toLinearMap := evenToCoeffs A d hd
  invFun := evenOfCoeffs A d hd
  left_inv := evenOfCoeffs_evenToCoeffs A d hd
  right_inv := evenToCoeffs_evenOfCoeffs A d hd

/-- The linear map forgetting positivity in the even-variable coefficient model. -/
def positiveCoeffsToCoeffs : PositiveCoeffs A →ₗ[R] Coeffs A where
  toFun := PositiveCoeffs.toCoeffs A
  map_add' := PositiveCoeffs.toCoeffs_add A
  map_smul' := PositiveCoeffs.toCoeffs_smul A

/-- Project a full divided-monomial coefficient family onto the positive-even model. -/
def coeffsToPositiveFun (x : Coeffs A) : PositiveCoeffs A :=
  (A.evenToEvenPositive (x 0),
    Finsupp.comapDomain posEmbedding x posEmbedding.injective.injOn)

/-- Projection to positive even-variable coefficients preserves addition. -/
theorem coeffsToPositiveFun_add (x y : Coeffs A) :
    coeffsToPositiveFun A (x + y) = coeffsToPositiveFun A x + coeffsToPositiveFun A y := by
  apply Prod.ext
  · change A.evenToEvenPositive ((x + y) 0) = _
    simp [coeffsToPositiveFun]
  · change Finsupp.comapDomain posEmbedding (x + y) posEmbedding.injective.injOn = _
    exact Finsupp.comapDomain_add_of_injective posEmbedding.injective x y

/-- Projection to positive even-variable coefficients preserves scalar multiplication. -/
theorem coeffsToPositiveFun_smul (r : R) (x : Coeffs A) :
    coeffsToPositiveFun A (r • x) = r • coeffsToPositiveFun A x := by
  apply Prod.ext
  · change A.evenToEvenPositive ((r • x) 0) = _
    simp [coeffsToPositiveFun]
  · apply Finsupp.ext
    intro i
    simp [coeffsToPositiveFun]

/-- The linear projection from full to positive even-variable coefficients. -/
def coeffsToPositive : Coeffs A →ₗ[R] PositiveCoeffs A where
  toFun := coeffsToPositiveFun A
  map_add' := coeffsToPositiveFun_add A
  map_smul' := coeffsToPositiveFun_smul A

/-- The explicit forward reindexing on the positive-even part of an even-variable extension. -/
def positiveToCoeffs (hd : Even d) :
    (algebra A d hd).evenPositivePart →ₗ[R] PositiveCoeffs A :=
  (coeffsToPositive A).comp <| (evenToCoeffs A d hd).comp (algebra A d hd).evenPositiveToEven

/-- The explicit inverse reindexing on positive even-variable coefficients. -/
def positiveOfCoeffs (hd : Even d) :
    PositiveCoeffs A →ₗ[R] (algebra A d hd).evenPositivePart :=
  (algebra A d hd).evenToEvenPositive.comp <|
    (evenOfCoeffs A d hd).comp (positiveCoeffsToCoeffs A)

/-- The positive-even divided-monomial coefficient reindexings are mutually inverse when the
adjoined even degree is positive. -/
theorem positiveOfCoeffs_positiveToCoeffs (hd : Even d) (hpos : 0 < d)
    (x : (algebra A d hd).evenPositivePart) :
    positiveOfCoeffs A d hd (positiveToCoeffs A d hd x) = x := sorry

/-- Reindexing after inserting positive divided-monomial coefficients is the identity. -/
theorem positiveToCoeffs_positiveOfCoeffs (hd : Even d) (hpos : 0 < d)
    (x : PositiveCoeffs A) :
    positiveToCoeffs A d hd (positiveOfCoeffs A d hd x) = x := sorry

/-- For positive even degree, the positive-even part of an even-variable extension is its
positive divided-monomial coefficient model. -/
@[stacks 09PI "even-variable positive-even reindexing"]
def positiveReindex (hd : Even d) (hpos : 0 < d) :
    (algebra A d hd).evenPositivePart ≃ₗ[R] PositiveCoeffs A where
  toLinearMap := positiveToCoeffs A d hd
  invFun := positiveOfCoeffs A d hd
  left_inv := positiveOfCoeffs_positiveToCoeffs A d hd hpos
  right_inv := positiveToCoeffs_positiveOfCoeffs A d hd hpos

/-- The transported total divided-power family on the positive even-variable extension. -/
def extensionGamma (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (n : ℕ)
    (x : (algebra A d hd).evenPositivePart) : (algebra A d hd).evenPart :=
  evenOfCoeffs A d hd <| gamma A gammaA n (positiveToCoeffs A d hd x)

/-- The transported positive-index divided powers on the positive even-variable extension. -/
def extensionGammaPos (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (n : ℕ+)
    (x : (algebra A d hd).evenPositivePart) : (algebra A d hd).evenPositivePart :=
  positiveOfCoeffs A d hd <|
    coeffsToPositive A (gamma A gammaA n (positiveToCoeffs A d hd x))

/-- In coefficient coordinates, the transported even-variable operation is the explicit
coefficient formula. -/
@[simp]
theorem evenToCoeffs_extensionGamma
    (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Even d)
    (n : ℕ) (x : (algebra A d hd).evenPositivePart) :
    evenToCoeffs A d hd (extensionGamma A d gammaA hd n x) =
      gamma A gammaA n (positiveToCoeffs A d hd x) := by
  exact evenToCoeffs_evenOfCoeffs A d hd _

/-- Positive coefficient coordinates expose the positive-index even-variable formula. -/
@[simp]
theorem positiveToCoeffs_extensionGammaPos
    (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Even d) (hpos : 0 < d)
    (n : ℕ+) (x : (algebra A d hd).evenPositivePart) :
    positiveToCoeffs A d hd (extensionGammaPos A d gammaA hd n x) =
      coeffsToPositive A (gamma A gammaA n (positiveToCoeffs A d hd x)) := by
  exact positiveToCoeffs_positiveOfCoeffs A d hd hpos _

/-- The transported total and positive-index even-variable operations agree after inclusion. -/
theorem extensionGamma_eq_extensionGammaPos
    (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Even d) (hpos : 0 < d)
    (n : ℕ+) (x : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd n x =
      (algebra A d hd).evenPositiveToEven (extensionGammaPos A d gammaA hd n x) := sorry

/-- Transported even-variable divided powers have the expected homogeneous degree. -/
theorem extensionGamma_degree (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) (n q : ℕ)
    (x : (algebra A d hd).piece (2 * (q + 1))) :
    ∃ y : (algebra A d hd).piece (2 * (n * (q + 1))),
      extensionGamma A d gammaA hd n ((algebra A d hd).evenPositiveHom q x) =
        (algebra A d hd).evenHom (n * (q + 1)) y := sorry

/-- The first transported even-variable divided power is positive-even inclusion. -/
theorem extensionGamma_one (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) (x : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd 1 x = (algebra A d hd).evenPositiveToEven x := sorry

/-- The zeroth transported even-variable divided power is the graded unit. -/
theorem extensionGamma_zero (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) (x : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd 0 x = (algebra A d hd).oneEven := sorry

/-- Transported even-variable divided powers obey the binomial multiplication law. -/
theorem extensionGamma_mul (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) (n m : ℕ)
    (x : (algebra A d hd).evenPositivePart) :
    (algebra A d hd).evenMul (extensionGamma A d gammaA hd n x)
        (extensionGamma A d gammaA hd m x) =
      Nat.choose (n + m) n • extensionGamma A d gammaA hd (n + m) x := sorry

/-- Transported even-variable divided powers are compatible with even multiplication. -/
theorem extensionGamma_evenMul (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) (n : ℕ) (x : (algebra A d hd).evenPart)
    (y : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd n ((algebra A d hd).evenMulPositive x y) =
      (algebra A d hd).evenMul ((algebra A d hd).evenPow x n)
        (extensionGamma A d gammaA hd n y) := sorry

/-- Higher transported even-variable divided powers vanish on products of odd homogeneous terms. -/
theorem extensionGamma_oddMul (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) {n : ℕ} (hn : 1 < n) (i j : ℕ)
    (x : (algebra A d hd).piece (2 * i + 1))
    (y : (algebra A d hd).piece (2 * j + 1)) :
    extensionGamma A d gammaA hd n ((algebra A d hd).oddMulTerm i j x y) = 0 := sorry

/-- Transported even-variable divided powers send sums to antidiagonal convolution. -/
theorem extensionGamma_add (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) (n : ℕ)
    (x y : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd n (x + y) =
      (Finset.antidiagonal n).sum fun ij ↦
        (algebra A d hd).evenMul (extensionGamma A d gammaA hd ij.1 x)
          (extensionGamma A d gammaA hd ij.2 y) := sorry

/-- Iterated transported even-variable divided powers use `Nat.uniformBell`. -/
theorem extensionGamma_comp (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) (n : ℕ) (m : ℕ+)
    (x : (algebra A d hd).evenPositivePart) :
    extensionGamma A d gammaA hd n (extensionGammaPos A d gammaA hd m x) =
      Nat.uniformBell n m • extensionGamma A d gammaA hd (n * (m : ℕ)) x := sorry

/-- Example 23.6.3 (Adjoining even variable) (Tag 09PI): the canonical divided powers on the
bundled algebra obtained by adjoining one variable of positive even degree. -/
@[stacks 09PI "canonical even-variable divided powers"]
def dividedPowers (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) :
    NonnegGradedAlgebra.DividedPowers (algebra A d hd) where
  gamma := extensionGamma A d gammaA hd
  gammaPos := extensionGammaPos A d gammaA hd
  gamma_eq_gammaPos := extensionGamma_eq_extensionGammaPos A d gammaA hd hpos
  gamma_degree := extensionGamma_degree A d gammaA hd hpos
  gamma_one := extensionGamma_one A d gammaA hd hpos
  gamma_zero := extensionGamma_zero A d gammaA hd hpos
  gamma_mul := extensionGamma_mul A d gammaA hd hpos
  gamma_evenMul := extensionGamma_evenMul A d gammaA hd hpos
  gamma_oddMul := extensionGamma_oddMul A d gammaA hd hpos
  gamma_add := extensionGamma_add A d gammaA hd hpos
  gamma_comp := extensionGamma_comp A d gammaA hd hpos

/-- Evaluation of the canonical even-variable divided powers is the transported explicit formula. -/
@[simp]
theorem dividedPowers_apply (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) (n : ℕ)
    (x : (algebra A d hd).evenPositivePart) :
    dividedPowers A d gammaA hd hpos n x = extensionGamma A d gammaA hd n x := by
  rfl

/-- The positive component of the canonical even-variable divided powers is explicit. -/
@[simp]
theorem dividedPowers_gammaPos (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) (n : ℕ+)
    (x : (algebra A d hd).evenPositivePart) :
    (dividedPowers A d gammaA hd hpos).gammaPos n x = extensionGammaPos A d gammaA hd n x := by
  rfl

/-- The coefficient coordinates of a candidate divided-power operation on the even-variable
extension. -/
def gammaCoords (hd : Even d) (delta : NonnegGradedAlgebra.DividedPowers (algebra A d hd))
    (n : ℕ) (z : PositiveCoeffs A) : Coeffs A :=
  evenToCoeffs A d hd (delta n (positiveOfCoeffs A d hd z))

/-- A divided-power structure on the positive even-variable extension is canonical when its
coordinates satisfy the coefficient-distribution formula, its divided monomials have the
expected divided powers, and its restriction to the base is `gammaA`. -/
structure IsCanonical (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d)
    (delta : NonnegGradedAlgebra.DividedPowers (algebra A d hd)) : Prop where
  /-- The coefficient family is the antidiagonal convolution of the constant divided powers and
  the positive-tail exponent-distribution formula. -/
  coefficients (n : ℕ) (z : PositiveCoeffs A) :
    gammaCoords A d hd delta n z =
      (Finset.antidiagonal n).sum fun ab ↦
        mul A (monomial A 0 (gammaA ab.1 z.constant)) (tailGamma A ab.2 z.tail)
  /-- Divided powers of `T ^ (i)` satisfy
  `gamma n (T ^ (i)) = Nat.uniformBell n i • T ^ (n * i)`. -/
  tPower (n : ℕ) (i : ℕ+) :
    gammaCoords A d hd delta n (Even.tPower A i) =
      Nat.uniformBell n (i : ℕ) • monomial A (n * (i : ℕ)) A.oneEven
  /-- The candidate divided powers restrict to the prescribed divided powers on the base. -/
  base (n : ℕ) (x : A.evenPositivePart) :
    delta n ((inclusion A d hd).evenPositiveMap x) =
      (inclusion A d hd).evenMap (gammaA n x)

/-- The explicit positive even-variable divided powers satisfy the coefficient-distribution,
divided-monomial, and base-restriction specifications. -/
theorem dividedPowers_isCanonical (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) :
    IsCanonical A d gammaA hd (dividedPowers A d gammaA hd hpos) := sorry

/-- Any positive even-variable divided-power structure satisfying the canonical coordinate
specification is the explicit transported structure. -/
theorem IsCanonical.eq_dividedPowers (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d)
    {delta : NonnegGradedAlgebra.DividedPowers (algebra A d hd)}
    (hdelta : IsCanonical A d gammaA hd delta) :
    delta = dividedPowers A d gammaA hd hpos := by
  apply NonnegGradedAlgebra.DividedPowers.ext
  intro n x
  apply (evenReindex A d hd).injective
  have h := hdelta.coefficients n (positiveToCoeffs A d hd x)
  dsimp only [gammaCoords] at h
  rw [positiveOfCoeffs_positiveToCoeffs A d hd hpos] at h
  exact h.trans (evenToCoeffs_extensionGamma A d gammaA hd n x).symm

/-- The uniqueness clause of Example 23.6.3 (Adjoining even variable) (Tag 09PI): the explicit
transported divided powers are the unique canonical structure on the bundled extension. -/
@[stacks 09PI "unique canonical even-variable divided powers"]
theorem existsUnique_dividedPowers
    (gammaA : NonnegGradedAlgebra.DividedPowers A) (hd : Even d) (hpos : 0 < d) :
    ∃! delta : NonnegGradedAlgebra.DividedPowers (algebra A d hd),
      IsCanonical A d gammaA hd delta := by
  refine ⟨dividedPowers A d gammaA hd hpos, dividedPowers_isCanonical A d gammaA hd hpos, ?_⟩
  intro delta hdelta
  exact hdelta.eq_dividedPowers A d gammaA hd hpos

/-- The positive even-variable extension bundled as a divided-power graded algebra. -/
@[stacks 09PI "bundled even-variable divided-power algebra"]
def dpAlgebra (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) : DividedPowerGradedAlgebra.{u, v} R :=
  DividedPowerGradedAlgebra.of (algebra A d hd) (dividedPowers A d gammaA hd hpos)

/-- The base inclusion into an even-variable extension preserves the transported divided powers. -/
theorem inclusion_map_gamma (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) (n : ℕ) (x : A.evenPositivePart) :
    (inclusion A d hd).evenMap (gammaA n x) =
      dividedPowers A d gammaA hd hpos n ((inclusion A d hd).evenPositiveMap x) := by
  exact (dividedPowers_isCanonical A d gammaA hd hpos).base n x |>.symm

/-- The canonical inclusion into an even-variable extension as a divided-power morphism. -/
def inclusionDP (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) :
    NonnegGradedAlgebra.DividedPowers.Hom gammaA (dividedPowers A d gammaA hd hpos) where
  toGradedHom := inclusion A d hd
  map_gamma := inclusion_map_gamma A d gammaA hd hpos

/-- Forgetting divided powers from the canonical even-variable inclusion recovers `inclusion`. -/
@[simp]
theorem inclusionDP_toGradedHom (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (hd : Even d) (hpos : 0 < d) :
    (inclusionDP A d gammaA hd hpos).toGradedHom = inclusion A d hd := by
  rfl

/-- The lift determined by the canonical divided monomials of a positive even target element
preserves divided powers. -/
theorem lift_map_gamma (gammaA : NonnegGradedAlgebra.DividedPowers A) (q : ℕ)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB)
    (z : B.piece (2 * (q + 1))) (n : ℕ)
    (x : (algebra A (2 * (q + 1)) (even_two_mul (q + 1))).evenPositivePart) :
    (lift A (2 * (q + 1)) (even_two_mul (q + 1)) g.toGradedHom
        (DividedMonomials.ofGamma gammaB q z)).evenMap
          (dividedPowers A (2 * (q + 1)) gammaA (even_two_mul (q + 1))
            (Nat.mul_pos (Nat.zero_lt_succ 1) (Nat.zero_lt_succ q)) n x) =
      gammaB n ((lift A (2 * (q + 1)) (even_two_mul (q + 1)) g.toGradedHom
        (DividedMonomials.ofGamma gammaB q z)).evenPositiveMap x) := sorry

/-- The canonical divided-power lift out of an extension by a variable in degree
`2 * (q + 1)`. -/
def liftDP (gammaA : NonnegGradedAlgebra.DividedPowers A) (q : ℕ)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB)
    (z : B.piece (2 * (q + 1))) :
    NonnegGradedAlgebra.DividedPowers.Hom
      (dividedPowers A (2 * (q + 1)) gammaA (even_two_mul (q + 1))
        (Nat.mul_pos (Nat.zero_lt_succ 1) (Nat.zero_lt_succ q))) gammaB where
  toGradedHom := lift A (2 * (q + 1)) (even_two_mul (q + 1)) g.toGradedHom
    (DividedMonomials.ofGamma gammaB q z)
  map_gamma := lift_map_gamma A gammaA q gammaB g z

/-- Forgetting divided powers from the canonical even-variable lift recovers evaluation at the
target divided monomials. -/
@[simp]
theorem liftDP_toGradedHom (gammaA : NonnegGradedAlgebra.DividedPowers A) (q : ℕ)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB)
    (z : B.piece (2 * (q + 1))) :
    (liftDP A gammaA q gammaB g z).toGradedHom =
      lift A (2 * (q + 1)) (even_two_mul (q + 1)) g.toGradedHom
        (DividedMonomials.ofGamma gammaB q z) := by
  rfl

/-- The positive even-variable divided-power lift restricts to its prescribed base morphism. -/
@[simp]
theorem inclusionDP_comp_liftDP (gammaA : NonnegGradedAlgebra.DividedPowers A) (q : ℕ)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB)
    (z : B.piece (2 * (q + 1))) :
    NonnegGradedAlgebra.DividedPowers.Hom.comp (liftDP A gammaA q gammaB g z)
      (inclusionDP A (2 * (q + 1)) gammaA (even_two_mul (q + 1))
        (Nat.mul_pos (Nat.zero_lt_succ 1) (Nat.zero_lt_succ q))) = g := by
  apply NonnegGradedAlgebra.DividedPowers.Hom.ext_toGradedHom
  exact lift_base A (2 * (q + 1)) (even_two_mul (q + 1)) g.toGradedHom
    (DividedMonomials.ofGamma gammaB q z)

/-- The positive even-variable divided-power lift sends the adjoined generator to the prescribed
element. -/
@[simp]
theorem liftDP_generator (gammaA : NonnegGradedAlgebra.DividedPowers A) (q : ℕ)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB)
    (z : B.piece (2 * (q + 1))) :
    (liftDP A gammaA q gammaB g z).toGradedHom.map (2 * (q + 1))
      (generator A (2 * (q + 1))) = z := by
  change (lift A _ _ g.toGradedHom (DividedMonomials.ofGamma gammaB q z)).map _ _ = z
  rw [lift_generator, DividedMonomials.ofGamma_generator]

/-- A divided-power morphism out of the positive even-variable extension is determined by its
base restriction and generator value. -/
theorem liftDP_unique (gammaA : NonnegGradedAlgebra.DividedPowers A) (q : ℕ)
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB)
    (z : B.piece (2 * (q + 1)))
    (f : NonnegGradedAlgebra.DividedPowers.Hom
      (dividedPowers A (2 * (q + 1)) gammaA (even_two_mul (q + 1))
        (Nat.mul_pos (Nat.zero_lt_succ 1) (Nat.zero_lt_succ q))) gammaB)
    (hbase : NonnegGradedAlgebra.DividedPowers.Hom.comp f
      (inclusionDP A (2 * (q + 1)) gammaA (even_two_mul (q + 1))
        (Nat.mul_pos (Nat.zero_lt_succ 1) (Nat.zero_lt_succ q))) = g)
    (hgenerator : f.toGradedHom.map (2 * (q + 1))
      (generator A (2 * (q + 1))) = z) :
    f = liftDP A gammaA q gammaB g z := sorry

namespace DividedMonomials

/-- The canonical half-degree index used to present a positive even degree as
`2 * (halfIndex d + 1)`. -/
def halfIndex (d : ℕ+) : ℕ :=
  (d : ℕ) / 2 - 1

/-- A positive even degree is twice the successor of its canonical half-degree index. -/
theorem two_mul_halfIndex_succ (d : ℕ+) (hd : Even (d : ℕ)) :
    2 * (halfIndex d + 1) = (d : ℕ) := by
  have hdiv : 2 * ((d : ℕ) / 2) = (d : ℕ) := Nat.two_mul_div_two_of_even hd
  have hpos := d.property
  change 2 * ((d : ℕ) / 2 - 1 + 1) = (d : ℕ)
  have hquot : 1 ≤ (d : ℕ) / 2 := by
    by_contra h
    have hz : (d : ℕ) / 2 = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero] at hdiv
    exact (Nat.ne_of_gt hpos) hdiv.symm
  rw [Nat.sub_add_cancel hquot]
  exact hdiv

/-- The homogeneous coefficient obtained by transporting the canonical divided power from the
half-degree presentation to an arbitrary positive even degree. -/
def ofEvenGammaCoefficient (B : NonnegGradedAlgebra.{u, v} R)
    (gamma : NonnegGradedAlgebra.DividedPowers B) (d : ℕ+) (hd : Even (d : ℕ))
    (x : B.piece d) (i : ℕ) : B.piece (i * (d : ℕ)) :=
  B.pieceCast (congrArg (fun e : ℕ ↦ i * e) (two_mul_halfIndex_succ d hd)) <|
    (ofGamma gamma (halfIndex d)
      (B.pieceCast (two_mul_halfIndex_succ d hd).symm x)).coefficient i

private theorem transportCoefficient_zero (B : NonnegGradedAlgebra.{u, v} R)
    {e f : ℕ} (h : e = f) (t : DividedMonomials B e) :
    B.pieceCast (congrArg (fun q : ℕ ↦ 0 * q) h) (t.coefficient 0) =
      cast (congrArg B.piece (Nat.zero_mul f).symm) GradedMonoid.GOne.one := by
  cases h
  exact t.coefficient_zero

private theorem transportCoefficient_mul (B : NonnegGradedAlgebra.{u, v} R)
    {e f : ℕ} (h : e = f) (t : DividedMonomials B e) (i j : ℕ) :
    cast (congrArg B.piece (Nat.add_mul i j f).symm)
        (GradedMonoid.GMul.mul
          (B.pieceCast (congrArg (fun q : ℕ ↦ i * q) h) (t.coefficient i))
          (B.pieceCast (congrArg (fun q : ℕ ↦ j * q) h) (t.coefficient j))) =
      Nat.choose (i + j) i •
        B.pieceCast (congrArg (fun q : ℕ ↦ (i + j) * q) h) (t.coefficient (i + j)) := by
  cases h
  exact t.coefficient_mul i j

private theorem transportCoefficient_generator (B : NonnegGradedAlgebra.{u, v} R)
    {e f : ℕ} (h : e = f) (t : DividedMonomials B e) :
    cast (congrArg B.piece (Nat.one_mul f))
        (B.pieceCast (congrArg (fun q : ℕ ↦ 1 * q) h) (t.coefficient 1)) =
      B.pieceCast h t.generator := by
  cases h
  rfl

private theorem pieceCast_symm_cancel (B : NonnegGradedAlgebra.{u, v} R)
    {e f : ℕ} (h : e = f) (x : B.piece f) :
    B.pieceCast h (B.pieceCast h.symm x) = x := by
  cases h
  rfl

/-- The zeroth transported even divided-monomial coefficient is the graded unit. -/
theorem ofEvenGammaCoefficient_zero (B : NonnegGradedAlgebra.{u, v} R)
    (gamma : NonnegGradedAlgebra.DividedPowers B) (d : ℕ+) (hd : Even (d : ℕ))
    (x : B.piece d) :
    ofEvenGammaCoefficient B gamma d hd x 0 =
      cast (congrArg B.piece (Nat.zero_mul (d : ℕ)).symm)
        GradedMonoid.GOne.one := by
  exact transportCoefficient_zero B (two_mul_halfIndex_succ d hd)
    (ofGamma gamma (halfIndex d) (B.pieceCast (two_mul_halfIndex_succ d hd).symm x))

/-- Transported even divided-monomial coefficients satisfy the binomial multiplication law. -/
theorem ofEvenGammaCoefficient_mul (B : NonnegGradedAlgebra.{u, v} R)
    (gamma : NonnegGradedAlgebra.DividedPowers B) (d : ℕ+) (hd : Even (d : ℕ))
    (x : B.piece d) (i j : ℕ) :
    cast (congrArg B.piece (Nat.add_mul i j (d : ℕ)).symm)
        (GradedMonoid.GMul.mul
          (ofEvenGammaCoefficient B gamma d hd x i)
          (ofEvenGammaCoefficient B gamma d hd x j)) =
      Nat.choose (i + j) i • ofEvenGammaCoefficient B gamma d hd x (i + j) := by
  exact transportCoefficient_mul B (two_mul_halfIndex_succ d hd)
    (ofGamma gamma (halfIndex d) (B.pieceCast (two_mul_halfIndex_succ d hd).symm x)) i j

/-- The divided-monomial family canonically induced by the divided powers of a homogeneous
element in an arbitrary positive even degree. -/
@[stacks 09PM "canonical divided monomials in positive even degree"]
def ofEvenGamma (B : NonnegGradedAlgebra.{u, v} R)
    (gamma : NonnegGradedAlgebra.DividedPowers B) (d : ℕ+) (hd : Even (d : ℕ))
    (x : B.piece d) : DividedMonomials B d where
  coefficient := ofEvenGammaCoefficient B gamma d hd x
  coefficient_zero := ofEvenGammaCoefficient_zero B gamma d hd x
  coefficient_mul := ofEvenGammaCoefficient_mul B gamma d hd x

/-- The coefficients of `ofEvenGamma` are the transported homogeneous divided powers of the
chosen element. -/
@[simp]
theorem ofEvenGamma_coefficient (B : NonnegGradedAlgebra.{u, v} R)
    (gamma : NonnegGradedAlgebra.DividedPowers B) (d : ℕ+) (hd : Even (d : ℕ))
    (x : B.piece d) (i : ℕ) :
    (ofEvenGamma B gamma d hd x).coefficient i =
      ofEvenGammaCoefficient B gamma d hd x i := by
  rfl

/-- The generator of `ofEvenGamma` is the chosen positive even homogeneous element. -/
@[simp]
theorem ofEvenGamma_generator (B : NonnegGradedAlgebra.{u, v} R)
    (gamma : NonnegGradedAlgebra.DividedPowers B) (d : ℕ+) (hd : Even (d : ℕ))
    (x : B.piece d) : (ofEvenGamma B gamma d hd x).generator = x := by
  change cast (congrArg B.piece (Nat.one_mul (d : ℕ)))
    (ofEvenGammaCoefficient B gamma d hd x 1) = x
  rw [ofEvenGammaCoefficient, transportCoefficient_generator, ofGamma_generator]
  exact pieceCast_symm_cancel B (two_mul_halfIndex_succ d hd) x

end DividedMonomials

/-- The graded-algebra evaluation map determined by a divided-power morphism on the base and a
homogeneous generator image in arbitrary positive even degree. -/
def liftPositiveMap (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (d : ℕ+) (hd : Even (d : ℕ))
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (x : B.piece d) :
    algebra A d hd ⟶ B :=
  lift A d hd g.toGradedHom (DividedMonomials.ofEvenGamma B gammaB d hd x)

/-- The arbitrary-positive-even-degree evaluation map preserves divided powers. -/
theorem liftPositiveMap_map_gamma (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (d : ℕ+) (hd : Even (d : ℕ))
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (x : B.piece d)
    (n : ℕ) (a : (algebra A d hd).evenPositivePart) :
    (liftPositiveMap A gammaA d hd gammaB g x).evenMap
        (dividedPowers A d gammaA hd d.2 n a) =
      gammaB n ((liftPositiveMap A gammaA d hd gammaB g x).evenPositiveMap a) := sorry

/-- The divided-power lift from an even-variable algebra in arbitrary positive even degree. -/
@[stacks 09PM "positive-even-degree divided-power lift"]
def liftPositiveDP (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (d : ℕ+) (hd : Even (d : ℕ))
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (x : B.piece d) :
    NonnegGradedAlgebra.DividedPowers.Hom
      (dividedPowers A d gammaA hd d.2) gammaB where
  toGradedHom := liftPositiveMap A gammaA d hd gammaB g x
  map_gamma := liftPositiveMap_map_gamma A gammaA d hd gammaB g x

/-- Forgetting divided powers from `liftPositiveDP` recovers its explicit evaluation map. -/
@[simp]
theorem liftPositiveDP_toGradedHom (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (d : ℕ+) (hd : Even (d : ℕ))
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (x : B.piece d) :
    (liftPositiveDP A gammaA d hd gammaB g x).toGradedHom =
      liftPositiveMap A gammaA d hd gammaB g x := by
  rfl

/-- The arbitrary-positive-even-degree divided-power lift restricts to its prescribed base
morphism. -/
@[simp]
theorem inclusionDP_comp_liftPositiveDP (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (d : ℕ+) (hd : Even (d : ℕ))
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (x : B.piece d) :
    NonnegGradedAlgebra.DividedPowers.Hom.comp
        (liftPositiveDP A gammaA d hd gammaB g x)
        (inclusionDP A d gammaA hd d.2) = g := by
  apply NonnegGradedAlgebra.DividedPowers.Hom.ext_toGradedHom
  exact lift_base A d hd g.toGradedHom (DividedMonomials.ofEvenGamma B gammaB d hd x)

/-- The arbitrary-positive-even-degree lift sends each source divided monomial to the
corresponding canonical divided power of the chosen generator image. -/
@[simp]
theorem liftPositiveDP_dividedMonomial (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (d : ℕ+) (hd : Even (d : ℕ))
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (x : B.piece d) (i : ℕ) :
    (liftPositiveDP A gammaA d hd gammaB g x).toGradedHom.map (i * (d : ℕ))
        (dividedMonomial A d i) =
      (DividedMonomials.ofEvenGamma B gammaB d hd x).coefficient i := by
  exact lift_dividedMonomial A d hd g.toGradedHom
    (DividedMonomials.ofEvenGamma B gammaB d hd x) i

/-- The arbitrary-positive-even-degree lift sends the adjoined generator to the chosen
homogeneous element. -/
@[simp]
theorem liftPositiveDP_generator (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (d : ℕ+) (hd : Even (d : ℕ))
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (x : B.piece d) :
    (liftPositiveDP A gammaA d hd gammaB g x).toGradedHom.map d (generator A d) = x := by
  change (lift A d hd g.toGradedHom (DividedMonomials.ofEvenGamma B gammaB d hd x)).map d _ = x
  rw [lift_generator, DividedMonomials.ofEvenGamma_generator]

/-- A divided-power morphism out of an arbitrary positive even-variable extension is determined
by its base restriction and generator value. -/
theorem liftPositiveDP_unique (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (d : ℕ+) (hd : Even (d : ℕ))
    {B : NonnegGradedAlgebra.{u, v} R} (gammaB : NonnegGradedAlgebra.DividedPowers B)
    (g : NonnegGradedAlgebra.DividedPowers.Hom gammaA gammaB) (x : B.piece d)
    (p : NonnegGradedAlgebra.DividedPowers.Hom
      (dividedPowers A d gammaA hd d.2) gammaB)
    (hbase : NonnegGradedAlgebra.DividedPowers.Hom.comp p
      (inclusionDP A d gammaA hd d.2) = g)
    (hgenerator : p.toGradedHom.map d (generator A d) = x) :
    p = liftPositiveDP A gammaA d hd gammaB g x := sorry

end Even

end NonnegGradedAlgebra.Adjoin
