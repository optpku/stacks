/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.Semilinear

/-!
# The canonical unit into a divided-power chain-DGA base change

An explicit base-change model determines a canonical semilinear map from the source: in a
nonnegative degree it sends `x` to the image of `1 ⊗ₜ x` under the recorded homogeneous
identification, and in a negative degree it is the zero map between the supported-zero pieces.
The construction depends on the supplied model and never chooses one from an existence theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe uR uS uA uB

namespace DividedPowerChainAlgebra

variable {R : Type uR} {S : Type uS}
variable [CommRing R] [CommRing S] [Algebra R S]

namespace BaseChange

variable {A : DividedPowerChainAlgebra.{uR, uA} R}

/-- The pure-tensor formula defining the scalar-extension unit preserves addition. -/
theorem unitPiece_add (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ)
    (x y : A.toChainDGAlgebra.nonnegativePiece n) :
    X.pieceIso n (1 ⊗ₜ[R] (x + y)) =
      X.pieceIso n (1 ⊗ₜ[R] x) + X.pieceIso n (1 ⊗ₜ[R] y) := sorry

/-- The pure-tensor formula defining the scalar-extension unit is semilinear along
`algebraMap R S`. -/
theorem unitPiece_smul (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ) (r : R)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    X.pieceIso n (1 ⊗ₜ[R] (r • x)) =
      algebraMap R S r • X.pieceIso n (1 ⊗ₜ[R] x) := sorry

/-- The canonical semilinear map from a natural-degree source piece into an explicit
scalar-extension model. -/
@[stacks 09PL "homogeneous scalar-extension unit"]
def unitPiece (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ) :
    A.toChainDGAlgebra.nonnegativePiece n →ₛₗ[algebraMap R S]
      X.algebra.toChainDGAlgebra.nonnegativePiece n where
  toFun := fun x ↦ X.pieceIso n (1 ⊗ₜ[R] x)
  map_add' := X.unitPiece_add n
  map_smul' := X.unitPiece_smul n

/-- Evaluation of the homogeneous scalar-extension unit is the recorded image of the pure
tensor `1 ⊗ₜ x`. -/
@[simp]
theorem unitPiece_apply (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    X.unitPiece n x = X.pieceIso n (1 ⊗ₜ[R] x) := sorry

/-- The homogeneous scalar-extension unit sends the source unit to the target unit. -/
@[simp]
theorem unitPiece_one (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) :
    X.unitPiece 0 A.toChainDGAlgebra.one =
      X.algebra.toChainDGAlgebra.one := sorry

/-- The homogeneous scalar-extension unit preserves multiplication in natural degrees. -/
@[simp]
theorem unitPiece_mul (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n m : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece n)
    (y : A.toChainDGAlgebra.nonnegativePiece m) :
    X.unitPiece (n + m) (A.toChainDGAlgebra.nonnegativeMul x y) =
      X.algebra.toChainDGAlgebra.nonnegativeMul
        (X.unitPiece n x) (X.unitPiece m y) := sorry

/-- The homogeneous scalar-extension unit commutes with the differential from a positive
natural degree. -/
@[simp]
theorem unitPiece_d (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ+)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    X.algebra.toChainDGAlgebra.nonnegativeDifferential n (X.unitPiece n x) =
      X.unitPiece ((n : ℕ) - 1)
        (A.toChainDGAlgebra.nonnegativeDifferential n x) := sorry

/-- The homogeneous scalar-extension unit preserves divided powers on every positive-even
piece. -/
@[simp]
theorem unitPiece_gammaPiece (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n d : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece (2 * (d + 1))) :
    X.algebra.gamma.gammaPiece n d (X.unitPiece (2 * (d + 1)) x) =
      X.unitPiece (2 * (n * (d + 1))) (A.gamma.gammaPiece n d x) := sorry

/-- A negative homogeneous source piece is a zero object by the source's nonnegative
support. -/
theorem source_isZero_negSucc (A : DividedPowerChainAlgebra.{uR, uA} R) (n : ℕ) :
    IsZero (A.toChainDGAlgebra.X (.negSucc n)) := sorry

/-- A negative homogeneous target piece is a zero object by the base-change model's
nonnegative support. -/
theorem target_isZero_negSucc (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ) :
    IsZero (X.algebra.toChainDGAlgebra.X (.negSucc n)) := sorry

/-- Every semilinear map out of a negative source piece is the zero map. -/
theorem negSuccMap_eq_zero (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ)
    (f : A.toChainDGAlgebra.X (.negSucc n) →ₛₗ[algebraMap R S]
      X.algebra.toChainDGAlgebra.X (.negSucc n)) :
    f = 0 := sorry

/-- The degreewise scalar-extension unit on all integer degrees.  Natural degrees use
`unitPiece`; negative degrees use the explicit zero semilinear map between supported-zero
pieces. -/
def unitMap (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) : ∀ i : ℤ,
    A.toChainDGAlgebra.X i →ₛₗ[algebraMap R S] X.algebra.toChainDGAlgebra.X i
  | .ofNat n => X.unitPiece n
  | .negSucc _ => 0

/-- In a natural degree, the integer-graded scalar-extension unit is `unitPiece`. -/
@[simp]
theorem unitMap_ofNat (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ) :
    X.unitMap n = X.unitPiece n := sorry

/-- In a negative degree, the integer-graded scalar-extension unit is the zero semilinear map. -/
@[simp]
theorem unitMap_negSucc (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ) :
    X.unitMap (.negSucc n) = 0 := sorry

/-- The integer-graded scalar-extension unit has the pure-tensor formula in every natural
degree. -/
@[simp]
theorem unitMap_apply_ofNat (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    X.unitMap n x = X.pieceIso n (1 ⊗ₜ[R] x) := sorry

/-- The integer-graded scalar-extension unit vanishes pointwise in every negative degree. -/
@[simp]
theorem unitMap_apply_negSucc (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ)
    (x : A.toChainDGAlgebra.X (.negSucc n)) :
    X.unitMap (.negSucc n) x = 0 := sorry

/-- The integer-graded scalar-extension unit commutes with the chain differential. -/
theorem unitMap_d (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    X.unitMap (n - 1) (A.toChainDGAlgebra.d n x) =
      X.algebra.toChainDGAlgebra.d n (X.unitMap n x) := sorry

/-- The integer-graded scalar-extension unit preserves the homogeneous unit. -/
theorem unitMap_one (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) :
    X.unitMap 0 A.toChainDGAlgebra.one =
      X.algebra.toChainDGAlgebra.one := sorry

/-- The integer-graded scalar-extension unit preserves homogeneous multiplication. -/
theorem unitMap_mul (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n m : ℤ)
    (x : A.toChainDGAlgebra.X n) (y : A.toChainDGAlgebra.X m) :
    X.unitMap (n + m) (A.toChainDGAlgebra.mul n m x y) =
      X.algebra.toChainDGAlgebra.mul n m (X.unitMap n x) (X.unitMap m y) := sorry

/-- The underlying semilinear chain-DGA homomorphism of the scalar-extension unit. -/
def unitChainHom (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) :
    ChainDGAlgebra.SemilinearHom (algebraMap R S) A.toChainDGAlgebra
      X.algebra.toChainDGAlgebra where
  map := X.unitMap
  map_d := X.unitMap_d
  map_one := X.unitMap_one
  map_mul := X.unitMap_mul

/-- The semilinear chain-DGA unit acts degreewise by `unitMap`. -/
@[simp]
theorem unitChainHom_apply (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    X.unitChainHom n x = X.unitMap n x := sorry

/-- The semilinear chain-DGA unit preserves the total divided-power operations. -/
theorem unitChainHom_map_gamma (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    Semilinear.evenMap X.unitChainHom (A.gamma n x) =
      X.algebra.gamma n (Semilinear.evenPositiveMap X.unitChainHom x) := sorry

/-- Tag 09PL and Tag 09PQ: the canonical semilinear scalar-extension unit associated to an
explicit divided-power chain-DGA base-change model. -/
@[stacks 09PL "canonical scalar-extension unit",
  stacks 09PQ "semilinear scalar-extension unit"]
def unit (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) :
    SemilinearHom (algebraMap R S) A X.algebra where
  toChainHom := X.unitChainHom
  map_gamma := X.unitChainHom_map_gamma

/-- The chain-DGA map underlying the scalar-extension unit is `unitChainHom`. -/
@[simp]
theorem unit_toChainHom (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) :
    X.unit.toChainHom = X.unitChainHom := sorry

/-- The homogeneous semilinear map underlying the scalar-extension unit is `unitMap`. -/
@[simp]
theorem unit_map (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (i : ℤ) :
    X.unit.toChainHom.map i = X.unitMap i := sorry

/-- The scalar-extension unit acts degreewise by the explicit integer-graded map. -/
@[simp]
theorem unit_apply (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    X.unit n x = X.unitMap n x := sorry

/-- The scalar-extension unit has the pure-tensor formula in every natural degree. -/
@[simp, stacks 09PL "scalar-extension unit pure-tensor formula"]
theorem unit_apply_ofNat (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    X.unit n x = X.pieceIso n (1 ⊗ₜ[R] x) := sorry

/-- The scalar-extension unit vanishes in every negative degree. -/
@[simp]
theorem unit_apply_negSucc (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ)
    (x : A.toChainDGAlgebra.X (.negSucc n)) :
    X.unit (.negSucc n) x = 0 := sorry

/-- The even homogeneous-piece map of the scalar-extension unit is the corresponding
`unitPiece`. -/
@[simp]
theorem unit_evenPieceMap (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (d : ℕ) :
    X.unit.evenPieceMap d = X.unitPiece (2 * d) := sorry

/-- The positive-even homogeneous-piece map of the scalar-extension unit is the corresponding
`unitPiece`. -/
@[simp]
theorem unit_evenPositivePieceMap (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (d : ℕ) :
    X.unit.evenPositivePieceMap d = X.unitPiece (2 * (d + 1)) := sorry

/-- The scalar-extension unit commutes with the differential. -/
@[simp]
theorem unit_d (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    X.unit (n - 1) (A.toChainDGAlgebra.d n x) =
      X.algebra.toChainDGAlgebra.d n (X.unit n x) := sorry

/-- The scalar-extension unit preserves the homogeneous unit. -/
@[simp]
theorem unit_one (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) :
    X.unit 0 A.toChainDGAlgebra.one =
      X.algebra.toChainDGAlgebra.one := sorry

/-- The scalar-extension unit preserves homogeneous multiplication. -/
@[simp]
theorem unit_mul (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n m : ℤ)
    (x : A.toChainDGAlgebra.X n) (y : A.toChainDGAlgebra.X m) :
    X.unit (n + m) (A.toChainDGAlgebra.mul n m x y) =
      X.algebra.toChainDGAlgebra.mul n m (X.unit n x) (X.unit m y) := sorry

/-- The scalar-extension unit preserves divided powers in the explicit homogeneous-piece
form. -/
@[simp, stacks 09PL "scalar-extension unit divided powers"]
theorem unit_gammaPiece (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n d : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece (2 * (d + 1))) :
    X.algebra.gamma.gammaPiece n d
        (X.unit.evenPositivePieceMap d x) =
      X.unit.evenPieceMap (n * (d + 1)) (A.gamma.gammaPiece n d x) := sorry

/-!
`chainComparison` is currently an ordinary divided-power chain-DGA homomorphism over `S`, not a
semilinear homomorphism bundled along `RingHom.id S`.  Naturality is therefore stated below as
an equality of degreewise semilinear maps along `algebraMap R S`; this is the strongest bundled
statement available without introducing an artificial cast between scalar-map indices.
-/

/-- Postcomposing a unit component with a canonical comparison preserves addition. -/
theorem postUnitMap_add (X Y : BaseChange.{uR, uS, uA, uB} (R' := S) A) (i : ℤ)
    (x y : A.toChainDGAlgebra.X i) :
    (X.chainComparison Y).toChainHom i (X.unit i (x + y)) =
      (X.chainComparison Y).toChainHom i (X.unit i x) +
        (X.chainComparison Y).toChainHom i (X.unit i y) := sorry

/-- Postcomposing a unit component with a canonical comparison remains semilinear along
`algebraMap R S`. -/
theorem postUnitMap_smul (X Y : BaseChange.{uR, uS, uA, uB} (R' := S) A) (i : ℤ) (r : R)
    (x : A.toChainDGAlgebra.X i) :
    (X.chainComparison Y).toChainHom i (X.unit i (r • x)) =
      algebraMap R S r • (X.chainComparison Y).toChainHom i (X.unit i x) := sorry

/-- The degreewise semilinear map obtained by postcomposing the unit of one model with the
canonical comparison to another model. -/
def postUnitMap (X Y : BaseChange.{uR, uS, uA, uB} (R' := S) A) (i : ℤ) :
    A.toChainDGAlgebra.X i →ₛₗ[algebraMap R S]
      Y.algebra.toChainDGAlgebra.X i where
  toFun := fun x ↦ (X.chainComparison Y).toChainHom i (X.unit i x)
  map_add' := X.postUnitMap_add Y i
  map_smul' := X.postUnitMap_smul Y i

/-- Evaluation of the postcomposed unit is pointwise composition with the canonical
comparison. -/
@[simp, stacks 09PL "base-change post-unit evaluation"]
theorem postUnitMap_apply (X Y : BaseChange.{uR, uS, uA, uB} (R' := S) A) (i : ℤ)
    (x : A.toChainDGAlgebra.X i) :
    X.postUnitMap Y i x = (X.chainComparison Y).toChainHom i (X.unit i x) := sorry

/-- Degreewise bundled naturality of the scalar-extension unit under canonical comparison. -/
@[simp, stacks 09PL "base-change post-unit naturality"]
theorem postUnitMap_eq_unitMap (X Y : BaseChange.{uR, uS, uA, uB} (R' := S) A) (i : ℤ) :
    X.postUnitMap Y i = Y.unitMap i := sorry

/-- The canonical comparison carries the unit of one base-change model to the unit of another
in every integer degree. -/
@[simp, stacks 09PL "base-change comparison carries units"]
theorem chainComparison_unit_apply (X Y : BaseChange.{uR, uS, uA, uB} (R' := S) A) (i : ℤ)
    (x : A.toChainDGAlgebra.X i) :
    (X.chainComparison Y).toChainHom i (X.unit i x) = Y.unit i x := sorry

/-- On a pure tensor in a natural-degree piece, the canonical comparison changes only the
chosen base-change model. -/
@[simp, stacks 09PL "base-change comparison on pure tensors"]
theorem chainComparison_pieceIso_tmul (X Y : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ)
    (r : S) (x : A.toChainDGAlgebra.nonnegativePiece n) :
    (X.chainComparison Y).toChainHom n (X.pieceIso n (r ⊗ₜ[R] x)) =
      Y.pieceIso n (r ⊗ₜ[R] x) := sorry

/-- On a natural-degree piece, comparison carries the pure-tensor unit map to the corresponding
unit map of the target model. -/
@[simp, stacks 09PL "base-change comparison on unit pieces"]
theorem chainComparison_unitPiece (X Y : BaseChange.{uR, uS, uA, uB} (R' := S) A) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    (X.chainComparison Y).toChainHom n (X.unitPiece n x) = Y.unitPiece n x := sorry

/-- The self-comparison fixes the scalar-extension unit pointwise. -/
@[simp, stacks 09PL "base-change self-comparison unit"]
theorem chainComparison_self_unit_apply (X : BaseChange.{uR, uS, uA, uB} (R' := S) A) (i : ℤ)
    (x : A.toChainDGAlgebra.X i) :
    (X.chainComparison X).toChainHom i (X.unit i x) = X.unit i x := sorry

/-- Successive canonical comparisons carry the source unit to the unit of the final
base-change model. -/
@[stacks 09PL "base-change comparison composition on units"]
theorem chainComparison_comp_unit_apply
    (X Y Z : BaseChange.{uR, uS, uA, uB} (R' := S) A) (i : ℤ)
    (x : A.toChainDGAlgebra.X i) :
    (Y.chainComparison Z).toChainHom i
        ((X.chainComparison Y).toChainHom i (X.unit i x)) =
      Z.unit i x := sorry

end BaseChange

end DividedPowerChainAlgebra
