/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Finite.ArithmeticFrobenius
public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect
public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.HatZ

/-!
# The profinite Galois group of a finite field

The completed integer map sends one to arithmetic Frobenius. Its reverse map
reads Frobenius exponents on the finite extensions of the given base field.
Both functions are specified data, independently of the inverse-law proofs.
-/

@[expose] public section

open CategoryTheory
noncomputable section
open ProfiniteGrp (integerGroup hatZ)
universe u

namespace FiniteField.ProfiniteGalois

variable (k : Type u) [Field k] [Finite k]

/-- The algebraic closure of a finite field is a Galois extension. -/
instance algebraicClosure_isGalois : IsGalois k (AlgebraicClosure k) := ⟨⟩

/-- Signed powers of the canonical arithmetic Frobenius. -/
def frobeniusPowers : integerGroup.{u} →* Gal(AlgebraicClosure k/k) :=
  letI : Fintype k := Fintype.ofFinite k
  { toFun := fun m ↦ arithmeticFrobenius k ^ (Multiplicative.toAdd m).down
    map_one' := sorry
    map_mul' := sorry }

/-- Complete the specified Frobenius-power homomorphism. -/
def frobeniusLift : hatZ.{u} ⟶
    InfiniteGalois.profiniteGalGrp k (AlgebraicClosure k) :=
  ProfiniteGrp.ProfiniteCompletion.lift
    (GrpCat.ofHom (frobeniusPowers k) :
      integerGroup.{u} ⟶ GrpCat.of (InfiniteGalois.profiniteGalGrp k (AlgebraicClosure k)))

/-- One finite integer quotient. -/
abbrev IntegerQuotient (H : FiniteIndexNormalSubgroup integerGroup.{u}) :=
  integerGroup.{u} ⧸ H.toSubgroup

/-- The testing extension has the degree of the specified finite quotient. -/
abbrev testField (H : FiniteIndexNormalSubgroup integerGroup.{u}) : Type u :=
  letI : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  ULift.{u} (FiniteField.Extension k (ringChar k) H.toSubgroup.index)

/-- The test field carries the native finite-extension scalar map from `k`. -/
instance testField_algebra (H : FiniteIndexNormalSubgroup integerGroup.{u}) :
    Algebra k (testField k H) := by
  letI : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  letI : NeZero H.toSubgroup.index := ⟨H.toSubgroup.index_ne_zero_of_finite⟩
  exact inferInstanceAs
    (Algebra k (ULift.{u} (FiniteField.Extension k (ringChar k) H.toSubgroup.index)))

/-- A native algebraic-embedding construction gives the test field in the algebraic closure. -/
def testEmbedding (H : FiniteIndexNormalSubgroup integerGroup.{u}) :
    testField k H →ₐ[k] AlgebraicClosure k := by
  letI : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  letI : NeZero H.toSubgroup.index := ⟨H.toSubgroup.index_ne_zero_of_finite⟩
  exact IsAlgClosed.lift

/-- Read the unique arithmetic-Frobenius exponent on the embedded finite extension.
The finite product also handles the trivial quotient, whose only coordinate is one. -/
def degreeCoordinate (H : FiniteIndexNormalSubgroup integerGroup.{u})
    (σ : Gal(AlgebraicClosure k/k)) : IntegerQuotient H := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  exact ∏ j : Fin H.toSubgroup.index,
    if σ.toAlgHom.comp (testEmbedding k H) =
        (arithmeticFrobenius k ^ j.val).toAlgHom.comp (testEmbedding k H)
    then QuotientGroup.mk (Multiplicative.ofAdd (ULift.up (j.val : ℤ)))
    else 1

/-- Finite-field Frobenius coordinates commute with maps of integer quotients. -/
theorem degreeCoordinate_naturality
    {H L : FiniteIndexNormalSubgroup integerGroup.{u}} (f : H ⟶ L)
    (σ : Gal(AlgebraicClosure k/k)) :
    (ProfiniteGrp.ProfiniteCompletion.diagram integerGroup).map f
        (degreeCoordinate k H σ) = degreeCoordinate k L σ := sorry

/-- The reverse function is the actual compatible tuple of finite-field evaluations. -/
def degreeTuple (σ : Gal(AlgebraicClosure k/k)) : hatZ.{u} :=
  ⟨fun H ↦ degreeCoordinate k H σ, fun _ _ f ↦ degreeCoordinate_naturality k f σ⟩

/-- The finite coordinate is its specified finite-field evaluation. -/
@[simp]
theorem degreeTuple_apply (σ : Gal(AlgebraicClosure k/k))
    (H : FiniteIndexNormalSubgroup integerGroup.{u}) :
    (degreeTuple k σ).val H = degreeCoordinate k H σ := rfl

/-- Signed Frobenius powers have their literal residue in every finite quotient. -/
theorem degreeCoordinate_frobeniusPowers
    (H : FiniteIndexNormalSubgroup integerGroup.{u}) (m : integerGroup.{u}) :
    degreeCoordinate k H (frobeniusPowers k m) = QuotientGroup.mk m := sorry

/-- Evaluating the completed Frobenius map recovers the original profinite integer. -/
theorem degreeTuple_frobeniusLift (z : hatZ.{u}) :
    degreeTuple k (frobeniusLift k z) = z := sorry

/-- Reassembling all finite-field restrictions recovers the Galois automorphism. -/
theorem frobeniusLift_degreeTuple (σ : Gal(AlgebraicClosure k/k)) :
    frobeniusLift k (degreeTuple k σ) = σ := sorry

theorem degreeTuple_mul (σ τ : Gal(AlgebraicClosure k/k)) :
    degreeTuple k (σ * τ) = degreeTuple k σ * degreeTuple k τ := sorry

/-- The coordinate evaluations are continuous for the Krull topology. -/
theorem degreeTuple_continuous : Continuous (degreeTuple k) := sorry

/-- Arithmetic Frobenius identifies the Galois group with profinite integers,
using specified functions in both directions. -/
def galoisEquiv : Gal(AlgebraicClosure k/k) ≃* (hatZ.{u} : Type u) where
  toFun := degreeTuple k
  invFun := frobeniusLift k
  left_inv := frobeniusLift_degreeTuple k
  right_inv := degreeTuple_frobeniusLift k
  map_mul' := degreeTuple_mul k

theorem galoisEquiv_continuous : Continuous (galoisEquiv k) :=
  degreeTuple_continuous k

theorem galoisEquiv_inverse_continuous : Continuous (galoisEquiv k).symm :=
  (frobeniusLift k).hom.continuous

/-- The specified completed Frobenius map is a bijection. -/
theorem frobeniusLift_bijective (k : Type u) [Field k] [Finite k] :
    Function.Bijective (frobeniusLift k).hom :=
  (galoisEquiv k).symm.bijective

end FiniteField.ProfiniteGalois
