/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation for filtered-complex functors

This leaf exposes the additive computations of the standard underlying, stage, associated-graded,
and graded-piece maps.  The functors themselves remain owned by `Complex/Functors` and the
category-independent constructions by `Filtration/Functors`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {K L : FilteredComplex A}

/-- The underlying-complex map sends zero to zero. -/
@[simp, stacks 012C "zero computation for underlying filtered-complex maps"]
theorem underlyingMap_zero : underlyingMap (0 : K ⟶ L) = 0 := sorry

/-- The underlying-complex map preserves addition. -/
@[simp, stacks 012C "addition computation for underlying filtered-complex maps"]
theorem underlyingMap_add (f g : K ⟶ L) :
    underlyingMap (f + g) = underlyingMap f + underlyingMap g := sorry

/-- The underlying-complex map preserves negation. -/
@[simp, stacks 012C "negation computation for underlying filtered-complex maps"]
theorem underlyingMap_neg (f : K ⟶ L) :
    underlyingMap (-f) = -underlyingMap f := sorry

/-- The underlying-complex map preserves subtraction. -/
@[simp, stacks 012C "subtraction computation for underlying filtered-complex maps"]
theorem underlyingMap_sub (f g : K ⟶ L) :
    underlyingMap (f - g) = underlyingMap f - underlyingMap g := sorry

/-- The underlying-complex map preserves natural scalar multiplication. -/
@[simp, stacks 012C "natural-scalar computation for underlying filtered-complex maps"]
theorem underlyingMap_nsmul (n : ℕ) (f : K ⟶ L) :
    underlyingMap (n • f) = n • underlyingMap f := sorry

/-- The underlying-complex map preserves integer scalar multiplication. -/
@[simp, stacks 012C "integer-scalar computation for underlying filtered-complex maps"]
theorem underlyingMap_zsmul (n : ℤ) (f : K ⟶ L) :
    underlyingMap (n • f) = n • underlyingMap f := sorry

/-- A fixed filtration-stage map sends zero to zero. -/
@[simp, stacks 012C "zero computation for filtered-complex stage maps"]
theorem stageMap_zero (p : ℤ) : stageMap (0 : K ⟶ L) p = 0 := sorry

/-- A fixed filtration-stage map preserves addition. -/
@[simp, stacks 012C "addition computation for filtered-complex stage maps"]
theorem stageMap_add (f g : K ⟶ L) (p : ℤ) :
    stageMap (f + g) p = stageMap f p + stageMap g p := sorry

/-- A fixed filtration-stage map preserves negation. -/
@[simp, stacks 012C "negation computation for filtered-complex stage maps"]
theorem stageMap_neg (f : K ⟶ L) (p : ℤ) :
    stageMap (-f) p = -stageMap f p := sorry

/-- A fixed filtration-stage map preserves subtraction. -/
@[simp, stacks 012C "subtraction computation for filtered-complex stage maps"]
theorem stageMap_sub (f g : K ⟶ L) (p : ℤ) :
    stageMap (f - g) p = stageMap f p - stageMap g p := sorry

/-- A fixed filtration-stage map preserves natural scalar multiplication. -/
@[simp, stacks 012C "natural-scalar computation for filtered-complex stage maps"]
theorem stageMap_nsmul (n : ℕ) (f : K ⟶ L) (p : ℤ) :
    stageMap (n • f) p = n • stageMap f p := sorry

/-- A fixed filtration-stage map preserves integer scalar multiplication. -/
@[simp, stacks 012C "integer-scalar computation for filtered-complex stage maps"]
theorem stageMap_zsmul (n : ℤ) (f : K ⟶ L) (p : ℤ) :
    stageMap (n • f) p = n • stageMap f p := sorry

variable [HasCokernels A]

/-- The associated-graded map sends zero to zero. -/
@[simp, stacks 012C "zero computation for associated-graded maps"]
theorem associatedGradedMap_zero : associatedGradedMap (0 : K ⟶ L) = 0 := sorry

/-- The associated-graded map preserves addition. -/
@[simp, stacks 012C "addition computation for associated-graded maps"]
theorem associatedGradedMap_add (f g : K ⟶ L) :
    associatedGradedMap (f + g) = associatedGradedMap f + associatedGradedMap g := sorry

/-- The associated-graded map preserves negation. -/
@[simp, stacks 012C "negation computation for associated-graded maps"]
theorem associatedGradedMap_neg (f : K ⟶ L) :
    associatedGradedMap (-f) = -associatedGradedMap f := sorry

/-- The associated-graded map preserves subtraction. -/
@[simp, stacks 012C "subtraction computation for associated-graded maps"]
theorem associatedGradedMap_sub (f g : K ⟶ L) :
    associatedGradedMap (f - g) = associatedGradedMap f - associatedGradedMap g := sorry

/-- The associated-graded map preserves natural scalar multiplication. -/
@[simp, stacks 012C "natural-scalar computation for associated-graded maps"]
theorem associatedGradedMap_nsmul (n : ℕ) (f : K ⟶ L) :
    associatedGradedMap (n • f) = n • associatedGradedMap f := sorry

/-- The associated-graded map preserves integer scalar multiplication. -/
@[simp, stacks 012C "integer-scalar computation for associated-graded maps"]
theorem associatedGradedMap_zsmul (n : ℤ) (f : K ⟶ L) :
    associatedGradedMap (n • f) = n • associatedGradedMap f := sorry

/-- A fixed graded-piece map sends zero to zero. -/
@[simp, stacks 012C "zero computation for graded-piece maps"]
theorem gradedPieceMap_zero (p : ℤ) : gradedPieceMap (0 : K ⟶ L) p = 0 := sorry

/-- A fixed graded-piece map preserves addition. -/
@[simp, stacks 012C "addition computation for graded-piece maps"]
theorem gradedPieceMap_add (f g : K ⟶ L) (p : ℤ) :
    gradedPieceMap (f + g) p = gradedPieceMap f p + gradedPieceMap g p := sorry

/-- A fixed graded-piece map preserves negation. -/
@[simp, stacks 012C "negation computation for graded-piece maps"]
theorem gradedPieceMap_neg (f : K ⟶ L) (p : ℤ) :
    gradedPieceMap (-f) p = -gradedPieceMap f p := sorry

/-- A fixed graded-piece map preserves subtraction. -/
@[simp, stacks 012C "subtraction computation for graded-piece maps"]
theorem gradedPieceMap_sub (f g : K ⟶ L) (p : ℤ) :
    gradedPieceMap (f - g) p = gradedPieceMap f p - gradedPieceMap g p := sorry

/-- A fixed graded-piece map preserves natural scalar multiplication. -/
@[simp, stacks 012C "natural-scalar computation for graded-piece maps"]
theorem gradedPieceMap_nsmul (n : ℕ) (f : K ⟶ L) (p : ℤ) :
    gradedPieceMap (n • f) p = n • gradedPieceMap f p := sorry

/-- A fixed graded-piece map preserves integer scalar multiplication. -/
@[simp, stacks 012C "integer-scalar computation for graded-piece maps"]
theorem gradedPieceMap_zsmul (n : ℤ) (f : K ⟶ L) (p : ℤ) :
    gradedPieceMap (n • f) p = n • gradedPieceMap f p := sorry

end CategoryTheory.FilteredComplex
