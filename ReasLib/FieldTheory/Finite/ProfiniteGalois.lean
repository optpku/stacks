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
    map_one' := zpow_zero _
    map_mul' := fun m n ↦ zpow_add _ (Multiplicative.toAdd m).down
      (Multiplicative.toAdd n).down }

open scoped Topology in
/-- Arithmetic Frobenius generates a dense subgroup for the Krull topology. -/
theorem frobeniusPowers_dense : DenseRange (frobeniusPowers k) := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨σ, hσ⟩
  have hN : (fun τ : Gal(AlgebraicClosure k/k) ↦ σ * τ) ⁻¹' U ∈ 𝓝 1 := by
    exact (continuous_const.mul continuous_id :
      Continuous (fun τ : Gal(AlgebraicClosure k/k) ↦ σ * τ)).continuousAt
        (by simpa using hU.mem_nhds hσ)
  obtain ⟨E, hfin, hnormal, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k (AlgebraicClosure k) _).mp hN
  letI := hfin
  letI := hnormal
  letI : Finite E := Module.finite_of_finite k
  letI : Fintype k := Fintype.ofFinite k
  obtain ⟨j, hj⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow k E).2
    (AlgEquiv.restrictNormalHom E σ)
  let m : integerGroup.{u} := Multiplicative.ofAdd (ULift.up (j.val : ℤ))
  have hresf : AlgEquiv.restrictNormalHom E (arithmeticFrobenius k) =
      frobeniusAlgEquivOfAlgebraic k E := by
    ext x
    exact (AlgEquiv.restrictNormal_commutes (arithmeticFrobenius k) E x).trans
      (map_pow E.val x (Fintype.card k)).symm
  have hres : AlgEquiv.restrictNormalHom E (frobeniusPowers k m) =
      AlgEquiv.restrictNormalHom E σ := by
    change AlgEquiv.restrictNormalHom E (arithmeticFrobenius k ^ (j.val : ℤ)) = _
    rw [map_zpow, hresf, zpow_natCast]
    exact hj
  have hfix : σ⁻¹ * frobeniusPowers k m ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    apply (AlgEquiv.restrictNormal_eq_one_iff E _).mp
    change AlgEquiv.restrictNormalHom E (σ⁻¹ * frobeniusPowers k m) = 1
    rw [map_mul, map_inv, hres, inv_mul_cancel]
  refine ⟨frobeniusPowers k m, ?_, m, rfl⟩
  simpa using hE hfix

/-- Complete the specified Frobenius-power homomorphism. -/
def frobeniusLift : hatZ.{u} ⟶
    InfiniteGalois.profiniteGalGrp k (AlgebraicClosure k) :=
  ProfiniteGrp.ProfiniteCompletion.lift
    (GrpCat.ofHom (frobeniusPowers k) :
      integerGroup.{u} ⟶ GrpCat.of (InfiniteGalois.profiniteGalGrp k (AlgebraicClosure k)))

private theorem frobeniusLift_eta (m : integerGroup.{u}) :
    frobeniusLift k (ProfiniteGrp.ProfiniteCompletion.etaFn integerGroup m) =
      frobeniusPowers k m := by
  exact ConcreteCategory.congr_hom (ProfiniteGrp.ProfiniteCompletion.lift_eta
    (GrpCat.ofHom (frobeniusPowers k) : integerGroup.{u} ⟶
      GrpCat.of (InfiniteGalois.profiniteGalGrp k (AlgebraicClosure k)))) m

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

private theorem degreeCoordinate_continuous_aux (H : FiniteIndexNormalSubgroup integerGroup.{u}) :
    @Continuous _ _ _ ⊥ (degreeCoordinate k H) := by
  classical
  letI : TopologicalSpace (IntegerQuotient H) := ⊥
  letI : Fintype k := Fintype.ofFinite k
  let E := (testEmbedding k H).fieldRange
  let e : testField k H ≃ₐ[k] E := (testEmbedding k H).equivFieldRange
  letI : Finite (testField k H) := by
    letI : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
    letI : NeZero H.toSubgroup.index := ⟨H.toSubgroup.index_ne_zero_of_finite⟩
    exact inferInstanceAs (Finite (ULift.{u} (FiniteField.Extension k (ringChar k)
      H.toSubgroup.index)))
  letI : Finite E := Finite.of_equiv (testField k H) e.toEquiv
  let f : Gal(E/k) → IntegerQuotient H :=
    fun τ ↦ ∏ j : Fin H.toSubgroup.index,
      if ((E.val.comp τ.toAlgHom).comp (testEmbedding k H).rangeRestrict) =
          (arithmeticFrobenius k ^ j.val).toAlgHom.comp (testEmbedding k H)
      then QuotientGroup.mk (Multiplicative.ofAdd (ULift.up (j.val : ℤ)))
      else 1
  have hf : Continuous f := continuous_of_discreteTopology
  convert hf.comp (InfiniteGalois.restrictNormalHom_continuous E) using 1
  funext σ
  have he : (E.val.comp (AlgEquiv.restrictNormalHom E σ).toAlgHom).comp
      (testEmbedding k H).rangeRestrict = σ.toAlgHom.comp (testEmbedding k H) := by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ E ((testEmbedding k H).rangeRestrict x)
  dsimp [degreeCoordinate, f]
  rw [he]

private theorem degreeCoordinate_frobeniusPowers_aux
    (H : FiniteIndexNormalSubgroup integerGroup.{u}) (m : integerGroup.{u}) :
    degreeCoordinate k H (frobeniusPowers k m) = QuotientGroup.mk m := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  letI : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  letI : NeZero H.toSubgroup.index := ⟨H.toSubgroup.index_ne_zero_of_finite⟩
  letI : Finite (testField k H) := inferInstanceAs
    (Finite (ULift.{u} (FiniteField.Extension k (ringChar k) H.toSubgroup.index)))
  letI : Algebra (testField k H) (AlgebraicClosure k) :=
    (testEmbedding k H).toRingHom.toAlgebra
  letI : IsScalarTower k (testField k H) (AlgebraicClosure k) :=
    IsScalarTower.of_algHom (testEmbedding k H)
  let g := frobeniusAlgEquivOfAlgebraic k (testField k H)
  have hg : orderOf g = H.toSubgroup.index := by
    rw [orderOf_frobeniusAlgEquivOfAlgebraic]
    exact (ULift.moduleEquiv : testField k H ≃ₗ[k]
      FiniteField.Extension k (ringChar k) H.toSubgroup.index).finrank_eq.trans
        (finrank_extension k (ringChar k) H.toSubgroup.index)
  let r := AlgEquiv.restrictNormalHom (F := k) (K₁ := AlgebraicClosure k) (testField k H)
  have hr : r (arithmeticFrobenius k) = g := by
    apply AlgEquiv.ext
    intro x
    apply (testEmbedding k H).injective
    exact (AlgEquiv.restrictNormal_commutes (arithmeticFrobenius k) (testField k H) x).trans
      (map_pow (testEmbedding k H) x (Fintype.card k)).symm
  have hcomp (σ τ : Gal(AlgebraicClosure k/k)) :
      σ.toAlgHom.comp (testEmbedding k H) = τ.toAlgHom.comp (testEmbedding k H) ↔
        r σ = r τ := by
    constructor
    · intro h
      apply AlgEquiv.ext
      intro x
      apply (testEmbedding k H).injective
      exact (AlgEquiv.restrictNormal_commutes σ (testField k H) x).trans
        ((DFunLike.congr_fun h x).trans
          (AlgEquiv.restrictNormal_commutes τ (testField k H) x).symm)
    · intro h
      ext x
      exact (AlgEquiv.restrictNormal_commutes σ (testField k H) x).symm.trans
        ((congrArg (fun e : Gal(testField k H/k) ↦ testEmbedding k H (e x)) h).trans
          (AlgEquiv.restrictNormal_commutes τ (testField k H) x))
  let t := (Multiplicative.toAdd m).down
  have hn : 0 < H.toSubgroup.index := NeZero.pos _
  have hnonneg := Int.emod_nonneg t (Int.natCast_ne_zero.mpr hn.ne')
  have hlt := Int.emod_lt_of_pos t (Int.natCast_pos.mpr hn)
  let j : Fin H.toSubgroup.index := ⟨(t % H.toSubgroup.index).toNat, by omega⟩
  have hj : (j.val : ℤ) = t % H.toSubgroup.index := Int.toNat_of_nonneg hnonneg
  have hmatch (i : Fin H.toSubgroup.index) :
      (frobeniusPowers k m).toAlgHom.comp (testEmbedding k H) =
          (arithmeticFrobenius k ^ i.val).toAlgHom.comp (testEmbedding k H) ↔ i = j := by
    rw [hcomp]
    change r (arithmeticFrobenius k ^ t) = r (arithmeticFrobenius k ^ i.val) ↔ _
    rw [map_zpow, map_pow, hr, ← zpow_natCast, zpow_eq_zpow_iff_modEq, hg]
    change t % (H.toSubgroup.index : ℤ) = (i.val : ℤ) % H.toSubgroup.index ↔ _
    have hi : (i.val : ℤ) % H.toSubgroup.index = i.val :=
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)
    rw [hi]
    constructor
    · intro h
      apply Fin.ext
      omega
    · rintro rfl
      exact hj.symm
  have hdeg : degreeCoordinate k H (frobeniusPowers k m) =
      QuotientGroup.mk (Multiplicative.ofAdd (ULift.up (j.val : ℤ))) := by
    simp only [degreeCoordinate, hmatch]
    simp
    rfl
  rw [hdeg]
  let a : integerGroup.{u} := Multiplicative.ofAdd (ULift.up (1 : ℤ))
  have ha (s : ℤ) : a ^ s = Multiplicative.ofAdd (ULift.up s) := by
    apply Multiplicative.toAdd.injective
    apply ULift.down_injective
    change s • (1 : ℤ) = s
    simp
  have hq : (QuotientGroup.mk (a ^ (j.val : ℤ)) : IntegerQuotient H) =
      QuotientGroup.mk (a ^ t) := by
    change QuotientGroup.mk' H.toSubgroup (a ^ (j.val : ℤ)) =
      QuotientGroup.mk' H.toSubgroup (a ^ t)
    rw [map_zpow, map_zpow, hj]
    exact zpow_mod_natCard _ t
  have hm : Multiplicative.ofAdd (ULift.up t) = m := by
    apply Multiplicative.toAdd.injective
    apply ULift.down_injective
    rfl
  simp only [ha] at hq
  rw [hm] at hq
  exact hq

/-- Finite-field Frobenius coordinates commute with maps of integer quotients. -/
theorem degreeCoordinate_naturality
    {H L : FiniteIndexNormalSubgroup integerGroup.{u}} (f : H ⟶ L)
    (σ : Gal(AlgebraicClosure k/k)) :
    (ProfiniteGrp.ProfiniteCompletion.diagram integerGroup).map f
        (degreeCoordinate k H σ) = degreeCoordinate k L σ := by
  letI : TopologicalSpace (IntegerQuotient H) := ⊥
  letI : TopologicalSpace (IntegerQuotient L) := ⊥
  letI : DiscreteTopology (IntegerQuotient H) := ⟨rfl⟩
  letI : DiscreteTopology (IntegerQuotient L) := ⟨rfl⟩
  have hmap : Continuous (fun x : IntegerQuotient H ↦
      ((ProfiniteGrp.ProfiniteCompletion.diagram integerGroup).map f x : IntegerQuotient L)) :=
    continuous_of_discreteTopology
  exact congrFun ((frobeniusPowers_dense k).equalizer
    (hmap.comp (degreeCoordinate_continuous_aux k H)) (degreeCoordinate_continuous_aux k L)
    (by
      funext m
      change (ProfiniteGrp.ProfiniteCompletion.diagram integerGroup).map f
        (degreeCoordinate k H (frobeniusPowers k m)) =
          degreeCoordinate k L (frobeniusPowers k m)
      rw [degreeCoordinate_frobeniusPowers_aux, degreeCoordinate_frobeniusPowers_aux]
      rfl)) σ

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
    degreeCoordinate k H (frobeniusPowers k m) = QuotientGroup.mk m :=
  degreeCoordinate_frobeniusPowers_aux k H m

/-- Evaluating the completed Frobenius map recovers the original profinite integer. -/
theorem degreeTuple_frobeniusLift (z : hatZ.{u}) :
    degreeTuple k (frobeniusLift k z) = z := by
  apply Subtype.ext
  funext H
  letI : TopologicalSpace (IntegerQuotient H) := ⊥
  letI : DiscreteTopology (IntegerQuotient H) := ⟨rfl⟩
  have hleft : Continuous (fun z : hatZ.{u} ↦ degreeCoordinate k H (frobeniusLift k z)) :=
    (degreeCoordinate_continuous_aux k H).comp (frobeniusLift k).hom.continuous
  have hright : Continuous (fun z : hatZ.{u} ↦ z.val H) :=
    (continuous_apply H).comp continuous_subtype_val
  exact congrFun ((ProfiniteGrp.ProfiniteCompletion.denseRange (G := integerGroup)).equalizer
    hleft hright (by
      funext m
      change degreeCoordinate k H
        (frobeniusLift k (ProfiniteGrp.ProfiniteCompletion.etaFn integerGroup m)) =
          QuotientGroup.mk m
      rw [frobeniusLift_eta, degreeCoordinate_frobeniusPowers])) z

/-- Reassembling all finite-field restrictions recovers the Galois automorphism. -/
theorem frobeniusLift_degreeTuple (σ : Gal(AlgebraicClosure k/k)) :
    frobeniusLift k (degreeTuple k σ) = σ := by
  have hsurj : Function.Surjective (frobeniusLift k) := by
    have hsubset : Set.range (frobeniusPowers k) ⊆ Set.range (frobeniusLift k) := by
      rintro _ ⟨m, rfl⟩
      exact ⟨ProfiniteGrp.ProfiniteCompletion.etaFn integerGroup m, frobeniusLift_eta k m⟩
    intro τ
    exact closure_minimal hsubset
      (frobeniusLift k).hom.continuous.isClosedMap.isClosed_range (frobeniusPowers_dense k τ)
  obtain ⟨z, rfl⟩ := hsurj σ
  rw [degreeTuple_frobeniusLift]

theorem degreeTuple_mul (σ τ : Gal(AlgebraicClosure k/k)) :
    degreeTuple k (σ * τ) = degreeTuple k σ * degreeTuple k τ := by
  apply (Function.LeftInverse.injective (degreeTuple_frobeniusLift k))
  rw [map_mul, frobeniusLift_degreeTuple, frobeniusLift_degreeTuple,
    frobeniusLift_degreeTuple]
  rfl

/-- The coordinate evaluations are continuous for the Krull topology. -/
theorem degreeTuple_continuous : Continuous (degreeTuple k) := by
  unfold degreeTuple
  exact (continuous_pi (fun H ↦ degreeCoordinate_continuous_aux k H)).subtype_mk _

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
