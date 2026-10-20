/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.CategoryTheory.Iso
public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.Chain
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Category

/-!
# Base change of divided-power graded algebras

This file owns scalar extension before any differential is chosen.  A model records explicit
homogeneous tensor-product identifications and their compatibility with the unit, multiplication,
and divided powers.  Canonical comparisons make downstream constructions independent of the
chosen model.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace DividedPowerGradedAlgebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A scalar-extension model of a divided-power graded algebra. -/
@[stacks 09PL "graded base-change model"]
structure BaseChange (A : DividedPowerGradedAlgebra.{u, w} R) where
  /-- The scalar-extended divided-power graded algebra. -/
  algebra : DividedPowerGradedAlgebra.{v, w} S
  /-- The scalar-extension identification on each homogeneous piece. -/
  pieceIso (n : ℕ) :
    (S ⊗[R] A.toGradedAlgebra.piece n) ≃ₗ[S] algebra.toGradedAlgebra.piece n
  /-- The tensor of the original unit is the unit after base change. -/
  map_one : pieceIso 0 (1 ⊗ₜ[R] (GradedMonoid.GOne.one : A.toGradedAlgebra.piece 0)) =
    (GradedMonoid.GOne.one : algebra.toGradedAlgebra.piece 0)
  /-- Homogeneous multiplication is the scalar extension of the original multiplication. -/
  map_mul (n m : ℕ) (r s : S) (x : A.toGradedAlgebra.piece n)
      (y : A.toGradedAlgebra.piece m) :
    pieceIso (n + m) ((r * s) ⊗ₜ[R] GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul (pieceIso n (r ⊗ₜ[R] x)) (pieceIso m (s ⊗ₜ[R] y))
  /-- Divided powers satisfy `γ_n(r ⊗ x) = r^n ⊗ γ_n(x)` on positive-even inputs. -/
  map_gamma (n d : ℕ) (r : S) (x : A.toGradedAlgebra.piece (2 * (d + 1))) :
    algebra.gamma.gammaPiece n d (pieceIso (2 * (d + 1)) (r ⊗ₜ[R] x)) =
      pieceIso (2 * (n * (d + 1))) ((r ^ n) ⊗ₜ[R] A.gamma.gammaPiece n d x)

namespace BaseChange

variable {A : DividedPowerGradedAlgebra.{u, w} R}

/-- The canonical semilinear map from a homogeneous source piece into a scalar-extension
model. -/
@[stacks 09PL "homogeneous map into a graded base-change model"]
def mapPiece (X : A.BaseChange (S := S)) (n : ℕ) :
    A.toGradedAlgebra.piece n → X.algebra.toGradedAlgebra.piece n :=
  fun x ↦ X.pieceIso n (1 ⊗ₜ[R] x)

end BaseChange

/-- Scalar extension along an explicit ring homomorphism.  This bridge fixes the algebra structure
induced by the given map once, so downstream APIs need not install local instances. -/
@[stacks 09PL "graded base change along a ring homomorphism"]
abbrev BaseChangeAlong (A : DividedPowerGradedAlgebra.{u, w} R) (f : R →+* S) :=
  @BaseChange R S _ _ f.toAlgebra A

namespace BaseChangeAlong

variable {A : DividedPowerGradedAlgebra.{u, w} R} {f : R →+* S}

/-- The target divided-power graded algebra of base change along an explicit ring map. -/
abbrev target (X : BaseChangeAlong A f) : DividedPowerGradedAlgebra.{v, w} S :=
  @BaseChange.algebra R S _ _ f.toAlgebra A X

/-- The canonical semilinear map from a homogeneous source piece into a base-change model. -/
@[stacks 09PL "homogeneous map into a graded base-change model"]
def mapPiece (X : BaseChangeAlong A f) (n : ℕ) :
    A.toGradedAlgebra.piece n → X.target.toGradedAlgebra.piece n :=
  @BaseChange.mapPiece R S _ _ f.toAlgebra A X n

/-- Map a natural-degree source piece into any divided-power graded algebra receiving a morphism
from the chosen base-change model. -/
def mapPieceTo (X : BaseChangeAlong A f)
    {B : DividedPowerGradedAlgebra.{v, w} S} (e : X.target ⟶ B) (n : ℕ) :
    A.toGradedAlgebra.piece n → B.toGradedAlgebra.piece n :=
  fun x ↦ e.toGradedHom.map n (X.mapPiece n x)

/-- Mapping a natural-degree piece through a target morphism is pointwise composition. -/
@[simp]
theorem mapPieceTo_apply (X : BaseChangeAlong A f)
    {B : DividedPowerGradedAlgebra.{v, w} S} (e : X.target ⟶ B) (n : ℕ)
    (x : A.toGradedAlgebra.piece n) :
    X.mapPieceTo e n x = e.toGradedHom.map n (X.mapPiece n x) := sorry

/-- The homogeneous base-change map extended by the identity on the zero pieces in negative
degrees. -/
def mapChainPiece (X : BaseChangeAlong A f) : ∀ i : ℤ,
    A.toGradedAlgebra.toChainGradedAlgebra.X i →
      X.target.toGradedAlgebra.toChainGradedAlgebra.X i
  | .ofNat n => X.mapPiece n
  | .negSucc _ => id

/-- Map an integer-graded source piece into any divided-power graded algebra receiving a
morphism from the chosen base-change model. -/
def mapChainPieceTo (X : BaseChangeAlong A f)
    {B : DividedPowerGradedAlgebra.{v, w} S} (e : X.target ⟶ B) (i : ℤ) :
    A.toGradedAlgebra.toChainGradedAlgebra.X i →
      B.toGradedAlgebra.toChainGradedAlgebra.X i :=
  fun x ↦ e.toGradedHom.toChainGradedHom.map i (X.mapChainPiece i x)

/-- Mapping through a target morphism is pointwise composition with the chain-graded extension
of that morphism. -/
@[simp]
theorem mapChainPieceTo_apply (X : BaseChangeAlong A f)
    {B : DividedPowerGradedAlgebra.{v, w} S} (e : X.target ⟶ B) (i : ℤ)
    (x : A.toGradedAlgebra.toChainGradedAlgebra.X i) :
    X.mapChainPieceTo e i x =
      e.toGradedHom.toChainGradedHom.map i (X.mapChainPiece i x) := sorry

/-- On a natural degree, the chain-graded base-change map is `mapPiece`. -/
@[simp]
theorem mapChainPiece_ofNat (X : BaseChangeAlong A f) (n : ℕ)
    (x : A.toGradedAlgebra.piece n) :
    X.mapChainPiece n x = X.mapPiece n x := sorry

/-- On a negative degree, the chain-graded base-change map is the identity of the zero piece. -/
@[simp]
theorem mapChainPiece_negSucc (X : BaseChangeAlong A f) (n : ℕ) (x : PUnit) :
    X.mapChainPiece (.negSucc n) x = x := sorry

/-- The homogeneous base-change map sends the source unit to the target unit. -/
@[simp]
theorem mapPiece_one (X : BaseChangeAlong A f) :
    X.mapPiece 0 (GradedMonoid.GOne.one : A.toGradedAlgebra.piece 0) =
      (GradedMonoid.GOne.one : X.target.toGradedAlgebra.piece 0) := sorry

/-- The homogeneous base-change map preserves multiplication. -/
@[simp]
theorem mapPiece_mul (X : BaseChangeAlong A f) (n m : ℕ)
    (x : A.toGradedAlgebra.piece n) (y : A.toGradedAlgebra.piece m) :
    X.mapPiece (n + m) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul (X.mapPiece n x) (X.mapPiece m y) := sorry

/-- The homogeneous base-change map preserves divided powers. -/
@[simp]
theorem mapPiece_gamma (X : BaseChangeAlong A f) (n d : ℕ)
    (x : A.toGradedAlgebra.piece (2 * (d + 1))) :
    X.target.gamma.gammaPiece n d (X.mapPiece (2 * (d + 1)) x) =
      X.mapPiece (2 * (n * (d + 1))) (A.gamma.gammaPiece n d x) := sorry

end BaseChangeAlong

namespace BaseChange

variable {A : DividedPowerGradedAlgebra.{u, w} R}

/-- The canonical comparison on a homogeneous piece of two base-change models. -/
@[stacks 09PL "homogeneous comparison of graded base-change models"]
def comparisonPiece (X Y : A.BaseChange (S := S)) (n : ℕ) :
    X.algebra.toGradedAlgebra.piece n ≃ₗ[S] Y.algebra.toGradedAlgebra.piece n :=
  (X.pieceIso n).symm.trans (Y.pieceIso n)

/-- Homogeneous comparisons preserve the graded unit. -/
theorem comparisonPiece_one (X Y : A.BaseChange (S := S)) :
    X.comparisonPiece Y 0
        (GradedMonoid.GOne.one : X.algebra.toGradedAlgebra.piece 0) =
      (GradedMonoid.GOne.one : Y.algebra.toGradedAlgebra.piece 0) := sorry

/-- Homogeneous comparisons preserve multiplication. -/
theorem comparisonPiece_mul (X Y : A.BaseChange (S := S)) (n m : ℕ)
    (x : X.algebra.toGradedAlgebra.piece n)
    (y : X.algebra.toGradedAlgebra.piece m) :
    X.comparisonPiece Y (n + m) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul (X.comparisonPiece Y n x) (X.comparisonPiece Y m y) := sorry

/-- The degreewise comparison of two base-change models as a graded-algebra homomorphism. -/
def gradedComparison (X Y : A.BaseChange (S := S)) :
    X.algebra.toGradedAlgebra ⟶ Y.algebra.toGradedAlgebra where
  map n := (X.comparisonPiece Y n).toLinearMap
  map_one := X.comparisonPiece_one Y
  map_mul := X.comparisonPiece_mul Y

/-- The graded comparison preserves the base-changed divided powers. -/
theorem gradedComparison_map_gamma (X Y : A.BaseChange (S := S)) (n : ℕ)
    (x : X.algebra.toGradedAlgebra.evenPositivePart) :
    (X.gradedComparison Y).evenMap (X.algebra.gamma n x) =
      Y.algebra.gamma n ((X.gradedComparison Y).evenPositiveMap x) := sorry

/-- The canonical divided-power graded comparison between two base-change models. -/
@[stacks 09PL "divided-power comparison of graded base-change models"]
def comparison (X Y : A.BaseChange (S := S)) : X.algebra ⟶ Y.algebra where
  toGradedHom := X.gradedComparison Y
  map_gamma := X.gradedComparison_map_gamma Y

/-- The comparison from a base-change model to itself is the identity. -/
@[simp]
theorem comparison_self (X : A.BaseChange (S := S)) :
    X.comparison X = 𝟙 X.algebra := sorry

/-- Comparisons of base-change models compose transitively. -/
@[simp]
theorem comparison_comp (X Y Z : A.BaseChange (S := S)) :
    X.comparison Y ≫ Y.comparison Z = X.comparison Z := sorry

/-- The forward and backward comparisons compose to the identity on the source model. -/
theorem comparison_hom_inv_id (X Y : A.BaseChange (S := S)) :
    X.comparison Y ≫ Y.comparison X = 𝟙 X.algebra := sorry

/-- The backward and forward comparisons compose to the identity on the target model. -/
theorem comparison_inv_hom_id (X Y : A.BaseChange (S := S)) :
    Y.comparison X ≫ X.comparison Y = 𝟙 Y.algebra := sorry

/-- The canonical isomorphism between two divided-power graded base-change models. -/
@[stacks 09PL "canonical graded scalar-extension comparison"]
def comparisonIso (X Y : A.BaseChange (S := S)) :
    CategoryTheory.Iso X.algebra Y.algebra where
  hom := X.comparison Y
  inv := Y.comparison X
  hom_inv_id := X.comparison_hom_inv_id Y
  inv_hom_id := X.comparison_inv_hom_id Y

/-- A divided-power graded algebra admits a scalar-extension model. -/
theorem nonempty (A : DividedPowerGradedAlgebra.{u, w} R) :
    Nonempty (A.BaseChange (S := S)) := sorry

end BaseChange

end DividedPowerGradedAlgebra
