module

public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.RationalPoint
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.Scheme.OverField.TensorPower
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Self exterior powers of degree-zero Chow classes

This module iterates the Chow exterior product of a degree-zero class along cartesian-monoidal
tensor powers of a scheme over a field.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- The inverse of the canonical tensor-to-product identification is proper on underlying
schemes. -/
instance tensorLeftIsoProd_inv_isProper
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom] (n : ℕ) :
    IsProper
      ((CartesianMonoidalCategory.tensorLeftIsoProd X).app (tensorPower X n)).inv.left := sorry

/-- Exterior multiplication by `alpha`, transported from the chosen categorical product to the
cartesian-monoidal tensor product used by `tensorPower`. -/
noncomputable def selfExteriorPowerStep
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (alpha : RelativeChow (fun _ ↦ (0 : ℤ)) X 0) (n : ℕ) :
    RelativeChow (fun _ ↦ (0 : ℤ)) (tensorPower X n) 0 →+
      RelativeChow (fun _ ↦ (0 : ℤ)) (tensorPower X (n + 1)) 0 :=
  (map (fun _ ↦ (0 : ℤ)) (X ⨯ tensorPower X n) (X ⊗ tensorPower X n)
      ((CartesianMonoidalCategory.tensorLeftIsoProd X).app (tensorPower X n)).inv 0).comp
    (exteriorProductPairing X (tensorPower X n) 0 0 alpha)

/-- The exterior-power step is exterior product followed by the canonical product-to-tensor
transport. -/
theorem selfExteriorPowerStep_apply
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (alpha : RelativeChow (fun _ ↦ (0 : ℤ)) X 0) (n : ℕ)
    (beta : RelativeChow (fun _ ↦ (0 : ℤ)) (tensorPower X n) 0) :
    selfExteriorPowerStep X alpha n beta =
      map (fun _ ↦ (0 : ℤ)) (X ⨯ tensorPower X n) (X ⊗ tensorPower X n)
          ((CartesianMonoidalCategory.tensorLeftIsoProd X).app (tensorPower X n)).inv 0
        (exteriorProductPairing X (tensorPower X n) 0 0 alpha beta) := sorry

/-- The left-recursive `n`-fold exterior product of a degree-zero Chow class, with the
degree-zero power given by the rational-point class of the monoidal unit. -/
noncomputable def selfExteriorPower
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (alpha : RelativeChow (fun _ ↦ (0 : ℤ)) X 0) :
    (n : ℕ) → RelativeChow (fun _ ↦ (0 : ℤ)) (tensorPower X n) 0
  | 0 => rationalPointClass (𝟙_ (SchemeOverField k)) (𝟙 _)
  | n + 1 =>
      selfExteriorPowerStep X alpha n (selfExteriorPower X alpha n)

/-- The zeroth self exterior power is the rational-point class of the monoidal unit. -/
theorem selfExteriorPower_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (alpha : RelativeChow (fun _ ↦ (0 : ℤ)) X 0) :
    selfExteriorPower X alpha 0 =
      rationalPointClass (𝟙_ (SchemeOverField k)) (𝟙 _) := sorry

/-- A successor self exterior power is the exterior product of the class with its preceding
power. -/
theorem selfExteriorPower_succ
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (alpha : RelativeChow (fun _ ↦ (0 : ℤ)) X 0) (n : ℕ) :
    selfExteriorPower X alpha (n + 1) =
      selfExteriorPowerStep X alpha n (selfExteriorPower X alpha n) := sorry

/-- For two rational points on a geometrically irreducible smooth projective scheme over a
field, every sufficiently large self exterior power of their degree-zero Chow-class difference
has finite additive order. -/
theorem rationalPointSub_exteriorPower_isTorsion
    {k : Type u} [Field k] (X : SchemeOverField k)
    [GeometricallyIrreducible X.hom] [Smooth X.hom] [Projective X.hom]
    (x x' : 𝟙_ (SchemeOverField k) ⟶ X) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsOfFinAddOrder
        (selfExteriorPower X (rationalPointClass X x - rationalPointClass X x') n) := sorry

end AlgebraicGeometry.ChowGroup
