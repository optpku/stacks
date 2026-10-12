/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.GradedModule
public import ReasLib.Algebra.DirectSum.NatToInt
public import ReasLib.RingTheory.Ideal.AssociatedGraded.StageClass

/-!
# The Associated Graded Module of an Ideal

This file equips the successive quotients `I ^ n M / I ^ (n + 1) M` with
their canonical homogeneous action by `gr_I(R)`.  It exposes both the
representative-level bilinear maps and Mathlib's standard graded-module
structures, so consumers need not reconstruct quotient actions or local
instances.
-/

@[expose] public section

noncomputable section

universe u v

namespace Ideal.AssociatedGraded

variable {R : Type u} [CommRing R]

/-- A degree-`d` ring-stage representative sends the degree-`n` module stage
into degree `d + n`. -/
theorem smul_mem_stage
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) {d n : ℕ} (x : stage I R d) (y : stage I M n) :
    (x : R) • (y : M) ∈ stage I M (d + n) := sorry

/-- Scalar multiplication by a fixed ring-stage representative, with its
codomain restricted to the shifted module stage. -/
def smulStage
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) (x : stage I R d) :
    stage I M n →ₗ[R] stage I M (d + n) :=
  LinearMap.codRestrict (stage I M (d + n))
    ((x : R) • (stage I M n).subtype)
    (smul_mem_stage I x)

/-- The stage action carries the next filtration stage into the next shifted
filtration stage. -/
theorem smulStage_denominator_le
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) (x : stage I R d) :
    denominator I M n ≤ Submodule.comap (smulStage I d n x)
      (denominator I M (d + n)) := sorry

/-- A fixed ring-stage representative acts linearly on the corresponding
associated graded module piece. -/
def pieceSMulFromStage
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) (x : stage I R d) :
    piece I M n →ₗ[R] piece I M (d + n) :=
  Submodule.mapQ (denominator I M n) (denominator I M (d + n))
    (smulStage I d n x) (smulStage_denominator_le I d n x)

/-- The action of a stage representative on a quotient representative is
represented by ordinary scalar multiplication in the ambient module. -/
@[simp] theorem pieceSMulFromStage_mk
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) (x : stage I R d) (y : stage I M n) :
    pieceSMulFromStage I d n x (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        ⟨(x : R) • (y : M), smul_mem_stage I x y⟩ := sorry

/-- The descended action is additive in its ring-stage representative. -/
theorem pieceSMulFromStage_add
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) (x y : stage I R d) :
    pieceSMulFromStage (M := M) I d n (x + y) =
      pieceSMulFromStage (M := M) I d n x +
        pieceSMulFromStage (M := M) I d n y := sorry

/-- The descended action is `R`-linear in its ring-stage representative. -/
theorem pieceSMulFromStage_smul
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) (r : R) (x : stage I R d) :
    pieceSMulFromStage (M := M) I d n (r • x) =
      r • pieceSMulFromStage (M := M) I d n x := sorry

/-- The action on the module quotient piece, linear in a ring-stage
representative. -/
def pieceSMulLinearFromStage
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) :
    stage I R d →ₗ[R] piece I M n →ₗ[R] piece I M (d + n) where
  toFun := pieceSMulFromStage (M := M) I d n
  map_add' := pieceSMulFromStage_add (M := M) I d n
  map_smul' := pieceSMulFromStage_smul (M := M) I d n

/-- Representatives from the next ring stage act trivially on every
associated graded module piece. -/
theorem pieceSMulLinearFromStage_denominator_le
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) :
    denominator I R d ≤
      LinearMap.ker (pieceSMulLinearFromStage (M := M) I d n) := sorry

/-- Homogeneous scalar multiplication
`(I ^ d / I ^ (d + 1)) →ₗ[R] (I ^ n M / I ^ (n + 1) M) →ₗ[R]
  I ^ (d + n) M / I ^ (d + n + 1) M`. -/
def pieceSMul
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) :
    piece I R d →ₗ[R] piece I M n →ₗ[R] piece I M (d + n) :=
  Submodule.liftQ (denominator I R d) (pieceSMulLinearFromStage I d n)
    (pieceSMulLinearFromStage_denominator_le (M := M) I d n)

/-- Multiplication of associated graded ring pieces is the homogeneous action
in the special case `M = R`. -/
def pieceMul (I : Ideal R) (d e : ℕ) :
    piece I R d →ₗ[R] piece I R e →ₗ[R] piece I R (d + e) :=
  pieceSMul I d e

/-- Homogeneous scalar multiplication computes by multiplication of chosen
stage representatives. -/
@[simp] theorem pieceSMul_mk
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) (x : stage I R d) (y : stage I M n) :
    pieceSMul I d n (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        ⟨(x : R) • (y : M), smul_mem_stage I x y⟩ := sorry

/-- Homogeneous scalar multiplication on the quotient pieces is associative
with homogeneous multiplication. -/
theorem pieceSMul_assoc
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d e n : ℕ)
    (a : piece I R d) (b : piece I R e) (m : piece I M n) :
    Nat.add_assoc d e n ▸ pieceSMul I d (e + n) a (pieceSMul I e n b m) =
      pieceSMul I (d + e) n (pieceMul I d e a b) m := sorry

/-- The homogeneous grade-to-piece equivalence preserves multiplication. -/
theorem gradeEquivPiece_mul
    (I : Ideal R) {d e : ℕ} (x : grade I d) (y : grade I e) :
    gradeEquivPiece I (d + e)
        ⟨(x : ring I) * (y : ring I), SetLike.mul_mem_graded x.2 y.2⟩ =
      pieceMul I d e (gradeEquivPiece I d x) (gradeEquivPiece I e y) := sorry

/-- The homogeneous grade-to-piece equivalence sends the degree-zero unit to
the class of `1` in `R / I`. -/
theorem gradeEquivPiece_one (I : Ideal R) :
    gradeEquivPiece I 0
        (⟨1, SetLike.one_mem_graded (grade I)⟩ : grade I 0) =
      (Submodule.Quotient.mk
        (⟨1, mem_stage_zero I R 1⟩ : stage I R 0) : piece I R 0) := sorry

/-- A homogeneous owner grade acts on a module piece through the canonical
grade-to-piece equivalence. -/
def gradeSMul
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) :
    grade I d →ₗ[R] piece I M n →ₗ[R] piece I M (d + n) :=
  (pieceSMul I d n).comp (gradeEquivPiece I d).toLinearMap

/-- The owner-grade action computes on an explicit stage class by multiplying
representatives. -/
@[simp] theorem gradeSMul_stageClass
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d n : ℕ) (x : stage I R d) (y : stage I M n) :
    gradeSMul I d n (stageClassLinear I d x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        ⟨(x : R) • (y : M), smul_mem_stage I x y⟩ := sorry

/-- The owner-grade action is associative with multiplication in the
associated graded ring. -/
theorem gradeSMul_assoc
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (d e n : ℕ)
    (x : grade I d) (y : grade I e) (m : piece I M n) :
    Nat.add_assoc d e n ▸ gradeSMul I d (e + n) x (gradeSMul I e n y m) =
      gradeSMul I (d + e) n
        ⟨(x : ring I) * (y : ring I), SetLike.mul_mem_graded x.2 y.2⟩ m := sorry

/-- The homogeneous grades of `gr_I(R)` act on the successive quotient
pieces of `M`. -/
noncomputable instance pieceGSMul
    {M : Type v} [AddCommGroup M] [Module R M] (I : Ideal R) :
    GradedMonoid.GSMul (fun n : ℕ ↦ ↥(grade I n)) (piece I M) where
  smul := fun x y ↦ gradeSMul I _ _ x y

/-- The degree-zero unit acts trivially on homogeneous module pieces. -/
theorem piece_one_smul
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (x : GradedMonoid (piece I M)) :
    (1 : GradedMonoid (fun n : ℕ ↦ ↥(grade I n))) • x = x := sorry

/-- Homogeneous multiplication is compatible with the action on homogeneous
module pieces. -/
theorem piece_mul_smul
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (a b : GradedMonoid (fun n : ℕ ↦ ↥(grade I n)))
    (x : GradedMonoid (piece I M)) :
    (a * b) • x = a • b • x := sorry

/-- The homogeneous action is a graded multiplicative action. -/
noncomputable instance pieceGMulAction
    {M : Type v} [AddCommGroup M] [Module R M] (I : Ideal R) :
    GradedMonoid.GMulAction (fun n : ℕ ↦ ↥(grade I n)) (piece I M) where
  one_smul := piece_one_smul I
  mul_smul := piece_mul_smul I

/-- Homogeneous scalar multiplication distributes over addition in a module
piece. -/
theorem piece_smul_add
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) {d n : ℕ} (a : grade I d) (x y : piece I M n) :
    gradeSMul I d n a (x + y) = gradeSMul I d n a x + gradeSMul I d n a y := sorry

/-- A homogeneous scalar sends zero to zero. -/
theorem piece_smul_zero
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) {d n : ℕ} (a : grade I d) :
    gradeSMul I d n a (0 : piece I M n) = 0 := sorry

/-- The homogeneous action is distributive in its module argument. -/
noncomputable instance pieceGdistribMulAction
    {M : Type v} [AddCommGroup M] [Module R M] (I : Ideal R) :
    DirectSum.GdistribMulAction (fun n : ℕ ↦ ↥(grade I n)) (piece I M) where
  smul_add := piece_smul_add I
  smul_zero := piece_smul_zero I

/-- Addition of homogeneous scalars distributes over the module action. -/
theorem piece_add_smul
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) {d n : ℕ} (a b : grade I d) (x : piece I M n) :
    gradeSMul I d n (a + b) x = gradeSMul I d n a x + gradeSMul I d n b x := sorry

/-- The zero homogeneous scalar acts trivially. -/
theorem piece_zero_smul
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) {d n : ℕ} (x : piece I M n) :
    gradeSMul I d n (0 : grade I d) x = 0 := sorry

/-- The successive quotients of the `I`-adic filtration form a graded module
over the homogeneous grades of `gr_I(R)`. -/
@[stacks 00K8 "associated graded module structure"]
noncomputable instance pieceGmodule
    {M : Type v} [AddCommGroup M] [Module R M] (I : Ideal R) :
    DirectSum.Gmodule (fun n : ℕ ↦ ↥(grade I n)) (piece I M) where
  add_smul := piece_add_smul I
  zero_smul := piece_zero_smul I

/-- The direct sum of the successive quotient pieces is canonically a module
over the quotient-Rees associated graded ring. -/
@[stacks 00K8 "associated graded module over the associated graded ring"]
noncomputable instance moduleRing
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Module (ring I) (gradedModule I M) :=
  Module.compHom (gradedModule I M)
    (DirectSum.decomposeRingEquiv (grade I)).toRingHom

/-- The `R ⧸ I`-action on the associated graded module is compatible with its
canonical action by `gr_I(R)`. -/
noncomputable instance scalarTowerQuotientRing
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsScalarTower (R ⧸ I) (ring I) (gradedModule I M) := sorry

/-- The natural degree-`n` submodule of the associated graded module. -/
def moduleGrade
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    Submodule (R ⧸ I) (gradedModule I M) :=
  LinearMap.range (DirectSum.lof (R ⧸ I) ℕ (piece I M) n)

/-- A quotient piece is canonically equivalent to the corresponding natural
degree submodule of the associated graded module. -/
noncomputable def pieceEquivModuleGrade
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    piece I M n ≃ₗ[R ⧸ I] moduleGrade I M n :=
  DirectSum.lofEquivRange (R := R ⧸ I) (piece I M) n

/-- The natural degree submodules decompose the associated graded module. -/
theorem moduleGrade_isInternal
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    DirectSum.IsInternal (moduleGrade I M) := sorry

/-- The natural degree submodules carry their canonical direct-sum
decomposition. -/
noncomputable instance moduleGradeDecomposition
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    DirectSum.Decomposition (moduleGrade I M) :=
  (moduleGrade_isInternal I M).chooseDecomposition

/-- The internal grading of `gr_I(R)` acts homogeneously on the natural
grading of `gr_I(M)`. -/
@[stacks 00K8 "internal associated graded module"]
noncomputable instance gradedSMulModuleGrade
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    SetLike.GradedSMul (grade I) (moduleGrade I M) := sorry

/-- The natural grading of an associated graded module, extended by zero to
negative integer degrees. -/
abbrev intGrade
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    ℤ → Submodule (R ⧸ I) (gradedModule I M) :=
  DirectSum.natToIntGrading (R := R ⧸ I) (piece I M)

/-- A nonnegative integer component of `intGrade` is the corresponding
natural degree submodule. -/
theorem intGrade_eq_moduleGrade_of_nonneg
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {d : ℤ} (hd : 0 ≤ d) :
    intGrade I M d = moduleGrade I M d.toNat := sorry

/-- A negative component of `intGrade` is zero. -/
theorem intGrade_eq_bot_of_neg
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {d : ℤ} (hd : d < 0) :
    intGrade I M d = ⊥ := sorry

/-- The degree-`n` quotient piece is canonically equivalent to degree `n` of
the integer-extended associated graded module. -/
noncomputable def pieceEquivIntGrade
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    piece I M n ≃ₗ[R ⧸ I] intGrade I M (n : ℤ) :=
  DirectSum.natToIntGradingEquiv (R := R ⧸ I) (piece I M) n

/-- The integer-degree comparison preserves the ambient direct-sum
representative. -/
@[simp] theorem pieceEquivIntGrade_coe
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (x : piece I M n) :
    ((pieceEquivIntGrade I M n x : intGrade I M (n : ℤ)) : gradedModule I M) =
      DirectSum.lof (R ⧸ I) ℕ (piece I M) n x := sorry

end Ideal.AssociatedGraded
