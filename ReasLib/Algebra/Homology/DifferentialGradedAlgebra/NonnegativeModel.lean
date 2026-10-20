/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.Chain
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Augmentation
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.HomologyAlgebra
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Nonnegative
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.OfPredifferential

/-!
# The extension-by-zero model of a nonnegative chain DGA

Restricting a strictly commutative chain DGA to natural degrees and extending those pieces by
zero gives a canonical chain-graded algebra.  Its differential is explicit, and square-zero
assembles it into a chain DGA.  There is a canonical map from this model to the original DGA;
when the original DGA is nonnegative, that map is a homology isomorphism in every degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The differential from a positive natural piece into the preceding piece of the
extension-by-zero grading. -/
def modelPositiveDifferential (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (n : ℕ+) :
    A.nonnegativePart.toChainGradedAlgebra.X (n : ℕ) →ₗ[R]
      A.nonnegativePart.toChainGradedAlgebra.X (((n : ℕ) : ℤ) + (-1)) :=
  (A.nonnegativePart.toChainGradedAlgebra.reindex
      (positiveDifferential_index n).symm).comp
    (A.nonnegativeDifferential n)

/-- The degree-`-1` map on the extension-by-zero grading induced by the original chain
differential. -/
def modelPredifferentialMap (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    ChainGradedAlgebra.HomogeneousMap A.nonnegativePart.toChainGradedAlgebra (-1)
  | .ofNat 0 => 0
  | .ofNat (n + 1) => A.modelPositiveDifferential ⟨n + 1, Nat.zero_lt_succ n⟩
  | .negSucc _ => 0

/-- On a positive natural degree, the model map is the original nonnegative differential. -/
@[simp]
theorem modelPredifferentialMap_ofNat_succ (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] (n : ℕ)
    (x : A.nonnegativePart.toChainGradedAlgebra.X (n + 1 : ℕ)) :
    A.modelPredifferentialMap (n + 1) x =
      A.modelPositiveDifferential ⟨n + 1, Nat.zero_lt_succ n⟩ x := sorry

/-- The model predifferential is zero in degree zero. -/
@[simp]
theorem modelPredifferentialMap_zero (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative]
    (x : A.nonnegativePart.toChainGradedAlgebra.X 0) :
    A.modelPredifferentialMap 0 x = 0 := sorry

/-- The model predifferential is zero in every negative degree. -/
@[simp]
theorem modelPredifferentialMap_negSucc (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] (n : ℕ) (x : PUnit) :
    A.modelPredifferentialMap (.negSucc n) x = 0 := sorry

/-- The extension-by-zero differential satisfies the graded Leibniz rule. -/
theorem modelPredifferentialMap_mem (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] :
    A.modelPredifferentialMap ∈
      ChainGradedAlgebra.derivationSubmodule
        A.nonnegativePart.toChainGradedAlgebra (-1) := sorry

/-- The predifferential on the extension-by-zero model of a chain DGA. -/
def modelPredifferential (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    ChainGradedAlgebra.Predifferential A.nonnegativePart.toChainGradedAlgebra :=
  ⟨A.modelPredifferentialMap, A.modelPredifferentialMap_mem⟩

/-- The model predifferential is square-zero. -/
theorem modelPredifferential_isSquareZero (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] :
    ChainGradedAlgebra.Predifferential.IsSquareZero A.modelPredifferential := sorry

/-- The chain DGA obtained by extending the nonnegative part of a chain DGA by zero. -/
@[stacks 09PS "extension-by-zero chain-DGA model"]
def nonnegativeModel (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    ChainDGAlgebra.{u, v} R :=
  ChainGradedAlgebra.Predifferential.toChainDGAlgebra
    A.modelPredifferential A.modelPredifferential_isSquareZero

/-- Graded commutativity descends to the extension-by-zero chain-DGA model. -/
theorem nonnegativeModel_mul_comm (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] {n m : ℤ}
    (x : A.nonnegativeModel.X n) (y : A.nonnegativeModel.X m) :
    A.nonnegativeModel.mul n m x y =
      cast (congrArg (fun i : ℤ ↦ (A.nonnegativeModel.X i : Type v))
          (add_comm m n))
        (((n * m).negOnePow : R) • A.nonnegativeModel.mul m n y x) := sorry

/-- Odd homogeneous elements square to zero in the extension-by-zero model. -/
theorem nonnegativeModel_sq_eq_zero_of_odd (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] {n : ℤ} (hn : Odd n)
    (x : A.nonnegativeModel.X n) :
    A.nonnegativeModel.mul n n x x = 0 := sorry

/-- The extension-by-zero model canonically inherits strict graded commutativity. -/
instance nonnegativeModelIsStrictlyCommutative (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] : A.nonnegativeModel.IsStrictlyCommutative where
  mul_comm := A.nonnegativeModel_mul_comm
  sq_eq_zero_of_odd := A.nonnegativeModel_sq_eq_zero_of_odd

/-- The homogeneous linear map from the extension-by-zero model to the original chain DGA. -/
def nonnegativeModelLinearMap (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    ∀ n : ℤ, A.nonnegativeModel.X n →ₗ[R] A.X n
  | .ofNat _ => LinearMap.id
  | .negSucc _ => 0

/-- The model comparison maps commute with the chain differentials. -/
theorem nonnegativeModelLinearMap_comm (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    ModuleCat.ofHom (A.nonnegativeModelLinearMap i) ≫ A.toChainComplex.d i j =
      A.nonnegativeModel.toChainComplex.d i j ≫
        ModuleCat.ofHom (A.nonnegativeModelLinearMap j) := sorry

/-- The canonical chain map from the extension-by-zero model to the original DGA. -/
def nonnegativeModelChainMap (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    A.nonnegativeModel.toChainComplex ⟶ A.toChainComplex where
  f n := ModuleCat.ofHom (A.nonnegativeModelLinearMap n)
  comm' := A.nonnegativeModelLinearMap_comm

/-- The model comparison preserves the homogeneous unit. -/
theorem nonnegativeModelChainMap_one (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] :
    (A.nonnegativeModelChainMap.f 0) A.nonnegativeModel.one = A.one := sorry

/-- The model comparison preserves homogeneous multiplication. -/
theorem nonnegativeModelChainMap_mul (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] (n m : ℤ)
    (x : A.nonnegativeModel.X n) (y : A.nonnegativeModel.X m) :
    A.nonnegativeModelChainMap.f (n + m) (A.nonnegativeModel.mul n m x y) =
      A.mul n m (A.nonnegativeModelChainMap.f n x)
        (A.nonnegativeModelChainMap.f m y) := sorry

/-- The canonical chain-DGA homomorphism from the extension-by-zero model to the original DGA. -/
@[stacks 09PS "comparison from the extension-by-zero DGA model"]
def nonnegativeModelHom (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    Hom A.nonnegativeModel A where
  toChainMap := A.nonnegativeModelChainMap
  map_one := A.nonnegativeModelChainMap_one
  map_mul := A.nonnegativeModelChainMap_mul

/-- The canonical model comparison acts as the identity in every natural degree. -/
@[simp]
theorem nonnegativeModelHom_ofNat (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] (n : ℕ) (x : A.X n) :
    A.nonnegativeModelHom n x = x := sorry

/-- For a nonnegative chain DGA, the model comparison induces a bijection on homology in every
degree. -/
theorem nonnegativeModelHom_homology_bijective (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] [A.IsNonnegative] (n : ℤ) :
    Function.Bijective (A.nonnegativeModelHom.homologyLinearMap n) := sorry

namespace Augmentation

variable {A : ChainDGAlgebra.{u, v} R} {S : Type v} [CommRing S] [Algebra R S]

/-- Pull an augmentation back to the canonical extension-by-zero model. -/
@[stacks 09PN "augmentation of the extension-by-zero DGA model"]
def nonnegativeModel (augmentation : Augmentation A S)
    [A.IsStrictlyCommutative] : Augmentation A.nonnegativeModel S :=
  augmentation.comp A.nonnegativeModelHom

/-- The chain map of the model augmentation is the model comparison followed by the original
augmentation. -/
@[simp]
theorem nonnegativeModel_toChainMap (augmentation : Augmentation A S)
    [A.IsStrictlyCommutative] :
    augmentation.nonnegativeModel.toChainMap =
      A.nonnegativeModelHom.toChainMap ≫ augmentation.toChainMap := sorry

/-- If the original DGA is nonnegative and its augmentation identifies zeroth homology with `S`,
then the induced augmentation of the extension-by-zero model has the same property. -/
theorem nonnegativeModel_homologyZeroMap_bijective
    (augmentation : Augmentation A S) [A.IsStrictlyCommutative] [A.IsNonnegative]
    (hH0 : Function.Bijective augmentation.homologyZeroMap) :
    Function.Bijective augmentation.nonnegativeModel.homologyZeroMap := sorry

end Augmentation

end ChainDGAlgebra
