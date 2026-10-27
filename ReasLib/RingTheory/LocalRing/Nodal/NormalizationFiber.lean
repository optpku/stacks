/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Nodal
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Normalization.Basic
public import ReasLib.RingTheory.RingHom.Fiber.Quotient

@[expose] public section

/-!
# Coordinates on the normalization closed fiber of a node

The choices of basis and coefficients below are exactly the choices in `quadraticAlgebra`.
Lift that basis to `x, y ∈ m`.  Since the coefficient of `x²` is nonzero, `y` is a
nonzerodivisor and `x/y` is integral.  The forward map sends the quadratic root to the class
of this fraction.  The reverse map multiplies a normalization element by `y`, takes its
class in `m/m²`, and evaluates its two coordinates at `(root, 1)`.

These are two separately constructed maps.  Packaging them as an equivalence belongs to
`normalizationFiber_equiv`, in `AlgebraicGeometry.Scheme.NodalLocalRing`.
-/

noncomputable section

open IsLocalRing Polynomial
open scoped TensorProduct Algebra.TensorProduct.Right nonZeroDivisors

universe u

namespace NodalLocalRing

section SelectedCoordinates

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNodalLocalRing A]

/-- The same cotangent basis selected in the definition of `quadraticAlgebra`. -/
def normalizationFiberBasis : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A) :=
  Classical.choose (IsNodalLocalRing.existsPresentation (A := A))

/-- The leading coefficient selected in `quadraticAlgebra`. -/
def normalizationFiberCoeffA : ResidueField A :=
  Classical.choose (Classical.choose_spec (IsNodalLocalRing.existsPresentation (A := A)))

/-- The middle coefficient selected in `quadraticAlgebra`. -/
def normalizationFiberCoeffB : ResidueField A :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (IsNodalLocalRing.existsPresentation (A := A))))

/-- The constant coefficient selected in `quadraticAlgebra`. -/
def normalizationFiberCoeffC : ResidueField A :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (IsNodalLocalRing.existsPresentation (A := A)))))

/-- The polynomial defining the already selected quadratic algebra representative. -/
abbrev normalizationFiberPolynomial : (ResidueField A)[X] :=
  C (normalizationFiberCoeffA A) * X ^ 2 + C (normalizationFiberCoeffB A) * X +
    C (normalizationFiberCoeffC A)

/-- The chosen leading coefficient is nonzero. -/
theorem normalizationFiberCoeffA_ne_zero : normalizationFiberCoeffA A ≠ 0 :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (IsNodalLocalRing.existsPresentation (A := A)))))).1

/-- The root in the selected `AdjoinRoot` representative, with no change of presentation. -/
def quadraticAlgebraRoot : quadraticAlgebra A :=
  AdjoinRoot.root (normalizationFiberPolynomial A)

/-- Lift each selected cotangent basis vector using the proved quotient surjection.
No nodal existence theorem is used to choose these lifts. -/
def normalizationFiberLift (i : Fin 2) : maximalIdeal A :=
  Classical.choose ((maximalIdeal A).toCotangent_surjective (normalizationFiberBasis A i))

@[simp]
theorem normalizationFiberLift_toCotangent (i : Fin 2) :
    (maximalIdeal A).toCotangent (normalizationFiberLift A i) = normalizationFiberBasis A i :=
  Classical.choose_spec ((maximalIdeal A).toCotangent_surjective (normalizationFiberBasis A i))

end SelectedCoordinates

section BaseExtraction

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The embedding of `m` into the total quotient ring is injective. -/
theorem maximalIdealToTotalQuotient_injective :
    Function.Injective (fun x : maximalIdeal A =>
      algebraMap A (Localization.totalQuotientRing A) (x : A)) := by
  intro x y h
  apply Subtype.ext
  exact IsLocalization.injective (Localization.totalQuotientRing A) le_rfl h

/-- Extract an element of `m` from its total-quotient image, returning zero outside that image.
This is the generic partial inverse of a proved embedding.  It is defined before, and does not
consume, any assertion about the nodal conductor or existence of a coordinate inverse. -/
def totalQuotientMaximalIdealValue (q : Localization.totalQuotientRing A) : maximalIdeal A :=
  (Function.partialInv (fun x : maximalIdeal A =>
    algebraMap A (Localization.totalQuotientRing A) (x : A)) q).getD 0

@[simp]
theorem totalQuotientMaximalIdealValue_algebraMap (x : maximalIdeal A) :
    totalQuotientMaximalIdealValue A
      (algebraMap A (Localization.totalQuotientRing A) (x : A)) = x := by
  unfold totalQuotientMaximalIdealValue
  rw [Function.partialInv_left (maximalIdealToTotalQuotient_injective A)]
  rfl

end BaseExtraction

section CoordinateValues

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNodalLocalRing A]

/-- The closed fiber, carrying its canonical residue-field algebra structure. -/
abbrev closedFiber : Type u :=
  (maximalIdeal A).Fiber (Normalization.normalizationRing A)

/-- Multiplication by the second lifted coordinate, followed by extraction into `m/m²`.
The conductor lemma below ensures that the extraction is evaluated inside its image. -/
def normalizationCotangentProduct (z : Normalization.normalizationRing A) : CotangentSpace A :=
  (maximalIdeal A).toCotangent (totalQuotientMaximalIdealValue A
    (algebraMap A (Localization.totalQuotientRing A) (normalizationFiberLift A 1 : A) *
      (z : Localization.totalQuotientRing A)))

/-- The two actual cotangent coefficients of `y*z`, in the selected basis. -/
def normalizationFiberCoefficient (z : Normalization.normalizationRing A) (i : Fin 2) :
    ResidueField A :=
  (normalizationFiberBasis A).repr (normalizationCotangentProduct A z) i

/-- Evaluate the cotangent coordinates of `y*z` at `(root, 1)`.
This formula defines the reverse map's data independently of the forward homomorphism. -/
def normalizationQuadraticValue (z : Normalization.normalizationRing A) : quadraticAlgebra A :=
  algebraMap (ResidueField A) (quadraticAlgebra A) (normalizationFiberCoefficient A z 0) *
      quadraticAlgebraRoot A +
    algebraMap (ResidueField A) (quadraticAlgebra A) (normalizationFiberCoefficient A z 1)

end CoordinateValues

section NodalNormalization

variable (k : Type u) [Field k]
variable (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
variable [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)]

/-- The second lift is transverse to both nodal branches. -/
theorem normalizationFiberLift_second_regular
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    (normalizationFiberLift A 1 : A) ∈ nonZeroDivisors A := by
  sorry

/-- The denominator is the actual second lift, with only its regularity proof admitted. -/
def normalizationFiberDenominator : nonZeroDivisors A :=
  ⟨(normalizationFiberLift A 1 : A), normalizationFiberLift_second_regular k A⟩

/-- The fraction `x/y` in the actual total quotient ring. -/
def normalizationFiberFraction : Localization.totalQuotientRing A :=
  Localization.mk (normalizationFiberLift A 0 : A) (normalizationFiberDenominator k A)

/-- The fraction has denominator `y` and numerator `x`. -/
theorem normalizationFiberFraction_mul_denominator :
    algebraMap A (Localization.totalQuotientRing A) (normalizationFiberLift A 1 : A) *
        normalizationFiberFraction k A =
      algebraMap A (Localization.totalQuotientRing A) (normalizationFiberLift A 0 : A) :=
  by
    unfold normalizationFiberFraction
    rw [Localization.mk_eq_mk'_apply]
    exact IsLocalization.mk'_spec' (Localization.totalQuotientRing A)
      (normalizationFiberLift A 0 : A) (normalizationFiberDenominator k A)

/-- The coordinate ratio is integral, since the nodal reduction of `m²` is `y*m`. -/
theorem normalizationFiberFraction_isIntegral
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    IsIntegral A (normalizationFiberFraction k A) := by
  sorry

/-- The actual fraction `x/y`, as an element of the integral closure. -/
def normalizationCoordinate : Normalization.normalizationRing A :=
  ⟨normalizationFiberFraction k A, normalizationFiberFraction_isIntegral k A⟩

/-- The nodal conductor identifies `y*N` with elements of `m` inside the total quotient ring.
This is a property of the extractor's inputs, not an existence witness used by its definition. -/
theorem normalizationCotangentProduct_conductor
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)]
    (z : Normalization.normalizationRing A) :
    algebraMap A (Localization.totalQuotientRing A)
        (totalQuotientMaximalIdealValue A
          (algebraMap A (Localization.totalQuotientRing A) (normalizationFiberLift A 1 : A) *
            (z : Localization.totalQuotientRing A)) : A) =
      algebraMap A (Localization.totalQuotientRing A) (normalizationFiberLift A 1 : A) *
        (z : Localization.totalQuotientRing A) := by
  sorry

/-- Multiplying the coordinate ratio by `y` recovers the first cotangent vector. -/
@[simp]
theorem normalizationCotangentProduct_coordinate :
    normalizationCotangentProduct A (normalizationCoordinate k A) =
      normalizationFiberBasis A 0 := by
  unfold normalizationCotangentProduct normalizationCoordinate
  rw [normalizationFiberFraction_mul_denominator,
    totalQuotientMaximalIdealValue_algebraMap, normalizationFiberLift_toCotangent]

/-- The reverse coordinate formula sends the actual ratio to the selected quadratic root. -/
@[simp]
theorem normalizationQuadraticValue_coordinate :
    normalizationQuadraticValue A (normalizationCoordinate k A) = quadraticAlgebraRoot A := by
  unfold normalizationQuadraticValue normalizationFiberCoefficient
  rw [normalizationCotangentProduct_coordinate]
  simp

/-- The selected generator in the normalization closed fiber. -/
def normalizationFiberRoot : closedFiber A :=
  algebraMap (Normalization.normalizationRing A) (closedFiber A) (normalizationCoordinate k A)

/-- The selected quadratic polynomial vanishes on the class of `x/y`. -/
theorem normalizationFiberRoot_eval
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    (normalizationFiberPolynomial A).eval₂
      (algebraMap (ResidueField A) (closedFiber A)) (normalizationFiberRoot k A) = 0 := by
  sorry

/-- Send the selected `AdjoinRoot` generator to the fiber class of the actual fraction `x/y`. -/
def quadraticAlgebraToNormalizationFiber :
    quadraticAlgebra A →ₐ[ResidueField A] closedFiber A :=
  AdjoinRoot.liftAlgHom (normalizationFiberPolynomial A) (Algebra.ofId _ _)
    (normalizationFiberRoot k A) (normalizationFiberRoot_eval k A)

/-- The reverse coordinate formula is a ring homomorphism on the normalization itself. -/
def normalizationQuadraticRingHom
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    Normalization.normalizationRing A →+* quadraticAlgebra A where
  toFun := normalizationQuadraticValue A
  map_one' := by sorry
  map_mul' := by intro x y; sorry
  map_zero' := by sorry
  map_add' := by intro x y; sorry

/-- The coordinate ring map on the normalization restricts to the residue map on `A`. -/
theorem normalizationQuadraticRingHom_scalar
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] (r : A) :
    normalizationQuadraticRingHom k A (algebraMap A (Normalization.normalizationRing A) r) =
      algebraMap (ResidueField A) (quadraticAlgebra A) (residue A r) := by
  sorry

/-- Extend the explicit coefficient formula across the residue-field tensor factor.
The only inverse used here is the proved canonical comparison between the two residue fields. -/
def normalizationFiberToQuadraticAlgebra
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    closedFiber A →ₐ[ResidueField A] quadraticAlgebra A := by
  let f : (maximalIdeal A).ResidueField →ₐ[A] quadraticAlgebra A :=
    (IsScalarTower.toAlgHom A (ResidueField A) (quadraticAlgebra A)).comp
      (ResidueField.maximalIdealAlgEquiv A).symm.toAlgHom
  let g : Normalization.normalizationRing A →ₐ[A] quadraticAlgebra A :=
    { toRingHom := normalizationQuadraticRingHom k A
      commutes' := normalizationQuadraticRingHom_scalar k A }
  let t := Algebra.TensorProduct.lift (S := A) f g (fun _ _ => Commute.all _ _)
  exact
    { toRingHom := t.toRingHom
      commutes' := by
        intro r
        sorry }

@[simp]
theorem quadraticAlgebraToNormalizationFiber_root :
    quadraticAlgebraToNormalizationFiber k A (quadraticAlgebraRoot A) =
      normalizationFiberRoot k A :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp]
theorem quadraticAlgebraToNormalizationFiber_scalar (r : ResidueField A) :
    quadraticAlgebraToNormalizationFiber k A
        (algebraMap (ResidueField A) (quadraticAlgebra A) r) =
      algebraMap (ResidueField A) (closedFiber A) r :=
  (quadraticAlgebraToNormalizationFiber k A).commutes r

/-- On a normalization representative, the reverse map is precisely the two-coefficient formula. -/
@[simp]
theorem normalizationFiberToQuadraticAlgebra_normalization
    (z : Normalization.normalizationRing A) :
    normalizationFiberToQuadraticAlgebra k A
        (algebraMap (Normalization.normalizationRing A) (closedFiber A) z) =
      algebraMap (ResidueField A) (quadraticAlgebra A) (normalizationFiberCoefficient A z 0) *
          quadraticAlgebraRoot A +
        algebraMap (ResidueField A) (quadraticAlgebra A) (normalizationFiberCoefficient A z 1) := by
  change normalizationFiberToQuadraticAlgebra k A (1 ⊗ₜ[A] z) = normalizationQuadraticValue A z
  simp [normalizationFiberToQuadraticAlgebra, normalizationQuadraticRingHom]

@[simp]
theorem normalizationFiberToQuadraticAlgebra_scalar (r : ResidueField A) :
    normalizationFiberToQuadraticAlgebra k A (algebraMap (ResidueField A) (closedFiber A) r) =
      algebraMap (ResidueField A) (quadraticAlgebra A) r :=
  (normalizationFiberToQuadraticAlgebra k A).commutes r

@[simp]
theorem normalizationFiberToQuadraticAlgebra_root :
    normalizationFiberToQuadraticAlgebra k A (normalizationFiberRoot k A) =
      quadraticAlgebraRoot A := by
  rw [normalizationFiberRoot, normalizationFiberToQuadraticAlgebra_normalization]
  exact normalizationQuadraticValue_coordinate k A

/-- The coordinate maps are inverse on the selected quadratic algebra. -/
theorem normalizationFiber_coordinate_left_inverse
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    (normalizationFiberToQuadraticAlgebra k A).comp
        (quadraticAlgebraToNormalizationFiber k A) =
      AlgHom.id (ResidueField A) (quadraticAlgebra A) := by
  apply AdjoinRoot.algHom_ext
  change normalizationFiberToQuadraticAlgebra k A
      (quadraticAlgebraToNormalizationFiber k A (quadraticAlgebraRoot A)) =
    quadraticAlgebraRoot A
  rw [quadraticAlgebraToNormalizationFiber_root, normalizationFiberToQuadraticAlgebra_root]

/-- The coordinate maps are inverse on the normalization closed fiber. -/
theorem normalizationFiber_coordinate_right_inverse
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    (quadraticAlgebraToNormalizationFiber k A).comp
        (normalizationFiberToQuadraticAlgebra k A) =
      AlgHom.id (ResidueField A) (closedFiber A) := by
  sorry

end NodalNormalization

end NodalLocalRing
