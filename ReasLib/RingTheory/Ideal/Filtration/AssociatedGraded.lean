/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.Filtration
public import ReasLib.RingTheory.Ideal.AssociatedGraded.StageClass
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated graded objects of ideal filtrations

This file attaches the successive quotients, their direct sum, and its canonical external grading
to an arbitrary ideal filtration. These constructions depend only on the filtration; applications
such as inverse-limit filtrations belong in separate files.
-/

@[expose] public section

noncomputable section

universe u v

namespace Ideal.Filtration

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {I : Ideal R}

/-- The degree-`n` quotient `Fⁿ / Fⁿ⁺¹` of an ideal filtration. -/
@[stacks 0GYM "graded piece of an ideal filtration"]
abbrev gradedPiece (F : I.Filtration M) (n : ℕ) : Type v :=
  F.N n ⧸ (F.N (n + 1)).submoduleOf (F.N n)

/-- The direct sum of the successive quotients of an ideal filtration. -/
@[stacks 0GYM "associated graded object of an ideal filtration"]
abbrev associatedGraded (F : I.Filtration M) : Type v :=
  DirectSum ℕ F.gradedPiece

/-- Every element of a filtration quotient is annihilated by `I`. -/
theorem gradedPiece_isTorsionBySet (F : I.Filtration M) (n : ℕ) :
    Module.IsTorsionBySet R (F.gradedPiece n) I := sorry

/-- A filtration quotient has its canonical module structure over `R ⧸ I`. -/
@[stacks 0GYM "quotient-ring module on a filtration graded piece", implicit_reducible]
noncomputable instance gradedPieceModuleQuotient
    (F : I.Filtration M) (n : ℕ) :
    Module (R ⧸ I) (F.gradedPiece n) :=
  (F.gradedPiece_isTorsionBySet n).module

/-- The quotient-ring action on a filtration piece is compatible with the original action. -/
noncomputable instance gradedPieceIsScalarTowerQuotient
    (F : I.Filtration M) (n : ℕ) :
    IsScalarTower R (R ⧸ I) (F.gradedPiece n) :=
  Module.IsTorsionBySet.isScalarTower (F.gradedPiece_isTorsionBySet n)

/-- The degree-`n` homogeneous submodule of the associated graded object of a filtration. -/
@[stacks 0GYM "grading of the associated graded object of an ideal filtration"]
def grade (F : I.Filtration M) (n : ℕ) :
    Submodule (R ⧸ I) F.associatedGraded :=
  LinearMap.range (DirectSum.lof (R ⧸ I) ℕ F.gradedPiece n)

/-- The canonical inclusion of a graded piece lands in the corresponding homogeneous subgroup. -/
@[simp]
theorem of_mem_grade (F : I.Filtration M) (n : ℕ) (x : F.gradedPiece n) :
    DirectSum.of F.gradedPiece n x ∈ F.grade n := sorry

namespace AssociatedGraded

/-- A degree-`d` ideal-power representative sends filtration stage `n` into stage `d + n`. -/
theorem smul_mem
    (F : I.Filtration M) {d n : ℕ}
    (x : Ideal.AssociatedGraded.stage I R d) (y : F.N n) :
    (x : R) • (y : M) ∈ F.N (d + n) := sorry

/-- Scalar multiplication by an ideal-power representative, restricted to filtration stages. -/
def smulStage
    (F : I.Filtration M) (d n : ℕ)
    (x : Ideal.AssociatedGraded.stage I R d) :
    F.N n →ₗ[R] F.N (d + n) :=
  LinearMap.codRestrict (F.N (d + n))
    ((x : R) • (F.N n).subtype) (smul_mem F x)

/-- The stage action carries the next filtration stage into the next target stage. -/
theorem smulStage_denominator_le
    (F : I.Filtration M) (d n : ℕ)
    (x : Ideal.AssociatedGraded.stage I R d) :
    (F.N (n + 1)).submoduleOf (F.N n) ≤
      Submodule.comap (smulStage F d n x)
        ((F.N (d + n + 1)).submoduleOf (F.N (d + n))) := sorry

/-- A fixed ideal-power representative acts on the corresponding filtration quotient. -/
def pieceSMulFromStage
    (F : I.Filtration M) (d n : ℕ)
    (x : Ideal.AssociatedGraded.stage I R d) :
    F.gradedPiece n →ₗ[R] F.gradedPiece (d + n) :=
  Submodule.mapQ
    ((F.N (n + 1)).submoduleOf (F.N n))
    ((F.N (d + n + 1)).submoduleOf (F.N (d + n)))
    (smulStage F d n x) (smulStage_denominator_le F d n x)

/-- The action on a filtration quotient is additive in the ideal-power representative. -/
theorem pieceSMulFromStage_add
    (F : I.Filtration M) (d n : ℕ)
    (x y : Ideal.AssociatedGraded.stage I R d) :
    pieceSMulFromStage F d n (x + y) =
      pieceSMulFromStage F d n x + pieceSMulFromStage F d n y := sorry

/-- The action on a filtration quotient is linear in the ideal-power representative. -/
theorem pieceSMulFromStage_smul
    (F : I.Filtration M) (d n : ℕ) (r : R)
    (x : Ideal.AssociatedGraded.stage I R d) :
    pieceSMulFromStage F d n (r • x) =
      r • pieceSMulFromStage F d n x := sorry

/-- The action on a filtration quotient, linear in the ideal-power representative. -/
def pieceSMulLinearFromStage
    (F : I.Filtration M) (d n : ℕ) :
    Ideal.AssociatedGraded.stage I R d →ₗ[R]
      F.gradedPiece n →ₗ[R] F.gradedPiece (d + n) where
  toFun := pieceSMulFromStage F d n
  map_add' := pieceSMulFromStage_add F d n
  map_smul' := pieceSMulFromStage_smul F d n

/-- Representatives in the next ideal-power stage act trivially on every filtration quotient. -/
theorem pieceSMulLinearFromStage_denominator_le
    (F : I.Filtration M) (d n : ℕ) :
    Ideal.AssociatedGraded.denominator I R d ≤
      LinearMap.ker (pieceSMulLinearFromStage F d n) := sorry

/-- Homogeneous scalar multiplication on the quotient pieces of an ideal filtration. -/
def pieceSMul
    (F : I.Filtration M) (d n : ℕ) :
    Ideal.AssociatedGraded.piece I R d →ₗ[R]
      F.gradedPiece n →ₗ[R] F.gradedPiece (d + n) :=
  Submodule.liftQ
    (Ideal.AssociatedGraded.denominator I R d)
    (pieceSMulLinearFromStage F d n)
    (pieceSMulLinearFromStage_denominator_le F d n)

/-- A homogeneous element of `gr_I(R)` acts on a filtration quotient through its canonical
successive-quotient presentation. -/
def gradeSMul
    (F : I.Filtration M) (d n : ℕ) :
    Ideal.AssociatedGraded.grade I d →ₗ[R]
      F.gradedPiece n →ₗ[R] F.gradedPiece (d + n) :=
  (pieceSMul F d n).comp
    (Ideal.AssociatedGraded.gradeEquivPiece I d).toLinearMap

/-- The homogeneous grades of `gr_I(R)` act on the quotient pieces of an ideal filtration. -/
noncomputable instance pieceGSMul (F : I.Filtration M) :
    GradedMonoid.GSMul
      (fun n : ℕ ↦ ↥(Ideal.AssociatedGraded.grade I n)) F.gradedPiece where
  smul := fun x y ↦ gradeSMul F _ _ x y

/-- The degree-zero homogeneous unit acts trivially on filtration quotient pieces. -/
theorem piece_one_smul
    (F : I.Filtration M) (x : GradedMonoid F.gradedPiece) :
    (1 : GradedMonoid (fun n : ℕ ↦ ↥(Ideal.AssociatedGraded.grade I n))) • x = x := sorry

/-- Homogeneous multiplication is associative with its action on filtration quotient pieces. -/
theorem piece_mul_smul
    (F : I.Filtration M)
    (a b : GradedMonoid (fun n : ℕ ↦ ↥(Ideal.AssociatedGraded.grade I n)))
    (x : GradedMonoid F.gradedPiece) :
    (a * b) • x = a • b • x := sorry

/-- The homogeneous action on filtration quotient pieces is a graded multiplicative action. -/
noncomputable instance pieceGMulAction (F : I.Filtration M) :
    GradedMonoid.GMulAction
      (fun n : ℕ ↦ ↥(Ideal.AssociatedGraded.grade I n)) F.gradedPiece where
  one_smul := piece_one_smul F
  mul_smul := piece_mul_smul F

/-- Homogeneous scalar multiplication distributes over addition in a filtration quotient. -/
theorem piece_smul_add
    (F : I.Filtration M) {d n : ℕ}
    (a : Ideal.AssociatedGraded.grade I d) (x y : F.gradedPiece n) :
    gradeSMul F d n a (x + y) =
      gradeSMul F d n a x + gradeSMul F d n a y := sorry

/-- A homogeneous scalar sends zero to zero in every filtration quotient. -/
theorem piece_smul_zero
    (F : I.Filtration M) {d n : ℕ}
    (a : Ideal.AssociatedGraded.grade I d) :
    gradeSMul F d n a (0 : F.gradedPiece n) = 0 := sorry

/-- The homogeneous action is distributive in its filtration-piece argument. -/
noncomputable instance pieceGdistribMulAction (F : I.Filtration M) :
    DirectSum.GdistribMulAction
      (fun n : ℕ ↦ ↥(Ideal.AssociatedGraded.grade I n)) F.gradedPiece where
  smul_add := piece_smul_add F
  smul_zero := piece_smul_zero F

/-- Addition of homogeneous scalars distributes over their action on filtration quotients. -/
theorem piece_add_smul
    (F : I.Filtration M) {d n : ℕ}
    (a b : Ideal.AssociatedGraded.grade I d) (x : F.gradedPiece n) :
    gradeSMul F d n (a + b) x =
      gradeSMul F d n a x + gradeSMul F d n b x := sorry

/-- The zero homogeneous scalar acts trivially on filtration quotients. -/
theorem piece_zero_smul
    (F : I.Filtration M) {d n : ℕ} (x : F.gradedPiece n) :
    gradeSMul F d n (0 : Ideal.AssociatedGraded.grade I d) x = 0 := sorry

/-- The successive quotients of an ideal filtration form a graded module over the homogeneous
pieces of `gr_I(R)`. -/
@[stacks 0GYM "graded action on the associated graded object of an ideal filtration"]
noncomputable instance pieceGmodule (F : I.Filtration M) :
    DirectSum.Gmodule
      (fun n : ℕ ↦ ↥(Ideal.AssociatedGraded.grade I n)) F.gradedPiece where
  add_smul := piece_add_smul F
  zero_smul := piece_zero_smul F

end AssociatedGraded

/-- The associated graded object of an ideal filtration is canonically a module over
`gr_I(R)`. -/
@[stacks 0GYM "associated graded module of an ideal filtration", implicit_reducible]
noncomputable instance moduleAssociatedGraded (F : I.Filtration M) :
    Module (Ideal.AssociatedGraded.ring I) F.associatedGraded :=
  Module.compHom F.associatedGraded
    (DirectSum.decomposeRingEquiv (Ideal.AssociatedGraded.grade I)).toRingHom

/-- The quotient-ring and associated-graded-ring actions form the canonical scalar tower. -/
noncomputable instance associatedGradedIsScalarTower
    (F : I.Filtration M) :
    IsScalarTower (R ⧸ I) (Ideal.AssociatedGraded.ring I) F.associatedGraded := sorry

/-- The homogeneous submodules give the canonical direct-sum decomposition. -/
theorem grade_isInternal (F : I.Filtration M) :
    DirectSum.IsInternal F.grade := sorry

/-- The associated graded object carries its canonical decomposition by filtration degree. -/
noncomputable instance gradeDecomposition (F : I.Filtration M) :
    DirectSum.Decomposition F.grade :=
  F.grade_isInternal.chooseDecomposition

/-- The internal grading of `gr_I(R)` acts homogeneously on the grading of an ideal filtration. -/
@[stacks 0GYM "internal grading of an associated graded filtration module"]
noncomputable instance gradedSMulGrade (F : I.Filtration M) :
    SetLike.GradedSMul (Ideal.AssociatedGraded.grade I) F.grade := sorry

end Ideal.Filtration
