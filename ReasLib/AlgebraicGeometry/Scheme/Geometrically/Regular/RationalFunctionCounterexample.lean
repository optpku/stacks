/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.FieldTheory.RatFunc.Degree

/-!
# Regular rational-function hypersurfaces in positive characteristic

This file packages two affine hypersurfaces over `RatFunc (ZMod p)` and records
their regularity and geometric reducedness or normality properties.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.RationalFunctionRegularityCounterexample

private theorem variety_spec (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [IsDomain A] [Algebra.FiniteType k A] :
    Variety (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))) := by
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  refine { toIsIntegral := ?_, toIsSeparated := ?_, toFiniteType := ?_ }
  · change IsIntegral (Spec (CommRingCat.of A))
    infer_instance
  · change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    infer_instance
  · change Scheme.Hom.FiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    infer_instance

private theorem isGeometricallyReduced_of_geometricallyReduced_spec
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (h : SchemeOverField.geometricallyReduced
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))) :
    Algebra.IsGeometricallyReduced k A := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  haveI : ∀ x : FieldExtension.baseChange k (AlgebraicClosure k) f,
      _root_.IsReduced ((FieldExtension.baseChange k (AlgebraicClosure k) f).presheaf.stalk x) :=
    fun x ↦ h _ (AlgebraicClosure k) x rfl
  haveI : IsReduced (FieldExtension.baseChange k (AlgebraicClosure k) f) :=
    isReduced_of_isReduced_stalk _
  haveI : IsReduced (Spec (CommRingCat.of (A ⊗[k] AlgebraicClosure k))) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso k A (AlgebraicClosure k)).inv
  haveI : _root_.IsReduced (A ⊗[k] AlgebraicClosure k) :=
    (affine_isReduced_iff (CommRingCat.of (A ⊗[k] AlgebraicClosure k))).1 inferInstance
  exact isReduced_of_injective
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) A).toRingHom
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) A).injective

private theorem normalRing_of_iso_spec (B : Type u) [CommRing B] (Y : Scheme.{u})
    (e : Y ≅ Spec (CommRingCat.of B))
    (h : ∀ y : Y, IsNormalRing (Y.presheaf.stalk y)) : IsNormalRing B := by
  have hlocal (p : PrimeSpectrum B) :
      IsDomain (Localization.AtPrime p.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
    let R := Y.presheaf.stalk (e.inv p)
    letI : IsNormalRing R := h (e.inv p)
    let m := IsLocalRing.maximalIdeal R
    let e0 : R ≃ₐ[R] Localization.AtPrime m :=
      IsLocalization.atUnits R m.primeCompl (fun x ↦ by simpa [m] using! fun a ↦ a)
    haveI : IsDomain (Localization.AtPrime m) :=
      IsNormalRing.isDomain_localizationAtPrime ⟨m, inferInstance⟩
    haveI : IsIntegrallyClosed (Localization.AtPrime m) :=
      IsNormalRing.isIntegrallyClosed_localizationAtPrime ⟨m, inferInstance⟩
    let e1 : R ≃+* Localization.AtPrime p.asIdeal :=
      (asIso (e.inv.stalkMap p)).commRingCatIsoToRingEquiv.trans
        (Spec.stalkIso (CommRingCat.of B) p).commRingCatIsoToRingEquiv
    let E := e0.toRingEquiv.symm.trans e1
    exact ⟨MulEquiv.isDomain (Localization.AtPrime m) E.symm.toMulEquiv,
      IsIntegrallyClosed.of_equiv E⟩
  exact ⟨fun p ↦ (hlocal p).1, fun p ↦ (hlocal p).2⟩

private theorem isGeometricallyNormal_of_geometricallyNormal_spec
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (h : SchemeOverField.geometricallyNormal
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))) :
    Algebra.IsGeometricallyNormal k A := by
  refine ⟨fun K _ _ ↦ ?_⟩
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let g := FieldExtension.specMap k K
  let e := pullbackSymmetry f g ≪≫ pullbackSpecIso k K A
  exact normalRing_of_iso_spec (K ⊗[k] A) _ e (fun y ↦ h _ K y rfl)

/-- The rational function field `𝔽_p(t)` in characteristic `p`. -/
abbrev BaseField (p : ℕ) [Fact p.Prime] : Type :=
  RatFunc (ZMod p)

namespace InseparablePoint

/-- The polynomial `x ^ p - t` over `𝔽_p(t)`. -/
abbrev polynomial (p : ℕ) [Fact p.Prime] : Polynomial (BaseField p) :=
  Polynomial.X ^ p - Polynomial.C (RatFunc.X : BaseField p)

/-- The quotient `𝔽_p(t)[x] / (x ^ p - t)`. -/
abbrev CoordinateRing (p : ℕ) [Fact p.Prime] : Type :=
  Polynomial (BaseField p) ⧸
    Ideal.span ({polynomial p} : Set (Polynomial (BaseField p)))

/-- The spectrum of `𝔽_p(t)[x] / (x ^ p - t)`. -/
def scheme (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (CoordinateRing p))

/-- The canonical structure morphism from `Spec(𝔽_p(t)[x] / (x ^ p - t))`
to `Spec(𝔽_p(t))`. -/
def toBase (p : ℕ) [Fact p.Prime] :
    scheme p ⟶ Spec (CommRingCat.of (BaseField p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (BaseField p) (CoordinateRing p)))

/-- The hypersurface `x ^ p = t` as a scheme over `𝔽_p(t)`. -/
def overBase (p : ℕ) [Fact p.Prime] :
    Over (Spec (CommRingCat.of (BaseField p))) :=
  Over.mk (toBase p)

/-- The degree at infinity of `t` is one, so it is not a `p`th power. -/
theorem polynomial_irreducible (p : ℕ) [Fact p.Prime] :
    Irreducible (polynomial p) := by
  apply X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime)
  intro b hb
  have hdegree : (p : ℤ) * RatFunc.intDegree b = 1 := by
    simpa only [RatFunc.intDegree_pow, RatFunc.intDegree_X] using
      congrArg RatFunc.intDegree hb
  have hdivInt : (p : ℤ) ∣ (1 : ℤ) := ⟨RatFunc.intDegree b, hdegree.symm⟩
  have hdiv : p ∣ 1 := by exact_mod_cast hdivInt
  exact (Nat.not_le_of_gt (Fact.out : p.Prime).one_lt)
    (Nat.le_of_dvd Nat.zero_lt_one hdiv)

/-- The coordinate ring `𝔽_p(t)[x] / (x ^ p - t)` is a domain. -/
instance instIsDomainCoordinateRing (p : ℕ) [Fact p.Prime] :
    IsDomain (CoordinateRing p) :=
  AdjoinRoot.isDomain_of_prime (polynomial_irreducible p).prime

/-- The hypersurface `x ^ p = t` is a variety over `𝔽_p(t)`. -/
theorem overBase_variety (p : ℕ) [Fact p.Prime] :
    Variety (overBase p) :=
  variety_spec (BaseField p) (CoordinateRing p)

/-- The variety structure on the hypersurface `x ^ p = t`. -/
instance instVarietyOverBase (p : ℕ) [Fact p.Prime] :
    Variety (overBase p) :=
  overBase_variety p

/-- The affine scheme `Spec(𝔽_p(t)[x] / (x ^ p - t))` is regular. -/
theorem scheme_regular (p : ℕ) [Fact p.Prime] :
    Scheme.Regular (scheme p) := by
  change Scheme.Regular (Spec (CommRingCat.of (CoordinateRing p)))
  letI : Fact (Irreducible (polynomial p)) := ⟨polynomial_irreducible p⟩
  letI : Field (CoordinateRing p) := inferInstanceAs (Field (AdjoinRoot (polynomial p)))
  refine ⟨fun x ↦ ⟨⟨⊤, isAffineOpen_top (Spec (CommRingCat.of (CoordinateRing p)))⟩,
    trivial, ?_⟩⟩
  exact IsRegularRing.of_ringEquiv
    (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing p))).symm.commRingCatIsoToRingEquiv

/-- The canonical regular scheme structure on `Spec(𝔽_p(t)[x] / (x ^ p - t))`. -/
instance instRegularScheme (p : ℕ) [Fact p.Prime] :
    Scheme.Regular (scheme p) :=
  scheme_regular p

/-- The algebra `𝔽_p(t)[x] / (x ^ p - t)` is not geometrically reduced over
`𝔽_p(t)`. -/
theorem coordinateRing_not_isGeometricallyReduced (p : ℕ) [Fact p.Prime] :
    ¬ Algebra.IsGeometricallyReduced (BaseField p) (CoordinateRing p) := by
  intro h
  let K := BaseField p
  let L := AlgebraicClosure K
  let A := AdjoinRoot (polynomial p)
  letI : Fact (Irreducible (polynomial p)) := ⟨polynomial_irreducible p⟩
  haveI : _root_.IsReduced (L ⊗[K] A) :=
    (Algebra.isGeometricallyReduced_field_iff K A).1 h
  haveI : CharP (L ⊗[K] A) p :=
    charP_of_injective_algebraMap (algebraMap K (L ⊗[K] A)).injective p
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K L (RatFunc.X : K)) (Fact.out : p.Prime).pos
  let r : A := AdjoinRoot.root (polynomial p)
  have hr : r ^ p = algebraMap K A (RatFunc.X : K) :=
    root_X_pow_sub_C_pow p (RatFunc.X : K)
  have hz : IsNilpotent (1 ⊗ₜ[K] r - a ⊗ₜ[K] (1 : A)) := by
    refine ⟨p, ?_⟩
    rw [sub_pow_char, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
      one_pow, one_pow, hr, ha, Algebra.TensorProduct.tmul_one_eq_one_tmul, sub_self]
  let pb : PowerBasis K A := AdjoinRoot.powerBasis'
    (Polynomial.monic_X_pow_sub_C (RatFunc.X : K) (Fact.out : p.Prime).ne_zero)
  have hdim : 1 < pb.dim := by
    simpa [pb, Polynomial.natDegree_X_pow_sub_C] using (Fact.out : p.Prime).one_lt
  let i0 : Fin pb.dim := ⟨0, Nat.zero_lt_one.trans hdim⟩
  let i1 : Fin pb.dim := ⟨1, hdim⟩
  have hb0 : pb.basis i0 = (1 : A) := by
    rw [pb.basis_eq_pow]
    rfl
  have hb1 : pb.basis i1 = r := by
    rw [pb.basis_eq_pow]
    change r ^ 1 = r
    rw [pow_one]
  have hcoeff0 : pb.basis.repr (1 : A) i1 = 0 := by
    rw [← hb0, pb.basis.repr_self]
    simp [i0, i1]
  have hcoeff1 : pb.basis.repr r i1 = 1 := by
    rw [← hb1, pb.basis.repr_self]
    simp
  have heq : 1 ⊗ₜ[K] r = a ⊗ₜ[K] (1 : A) := sub_eq_zero.mp hz.eq_zero
  have hcoeff := congrArg (fun z ↦ (pb.basis.baseChange L).repr z i1) heq
  rw [Module.Basis.baseChange_repr_tmul L pb.basis (1 : L) r i1,
    Module.Basis.baseChange_repr_tmul L pb.basis a (1 : A) i1,
    hcoeff1, hcoeff0, one_smul, zero_smul] at hcoeff
  exact one_ne_zero hcoeff

/-- The hypersurface `x ^ p = t` is not geometrically reduced over `𝔽_p(t)`. -/
theorem overBase_not_geometricallyReduced (p : ℕ) [Fact p.Prime] :
    ¬ SchemeOverField.geometricallyReduced (overBase p) := by
  intro h
  exact coordinateRing_not_isGeometricallyReduced p
    (isGeometricallyReduced_of_geometricallyReduced_spec (BaseField p) (CoordinateRing p) h)

end InseparablePoint

namespace Cusp

/-- The polynomial `y ^ 2 - x ^ p + t` over `𝔽_p(t)`, with `x = X 0` and
`y = X 1`. -/
abbrev equation (p : ℕ) [Fact p.Prime] :
    MvPolynomial (Fin 2) (BaseField p) :=
  MvPolynomial.X (1 : Fin 2) ^ 2 -
    MvPolynomial.X (0 : Fin 2) ^ p +
    MvPolynomial.C (RatFunc.X : BaseField p)

/-- The quotient `𝔽_p(t)[x, y] / (y ^ 2 - x ^ p + t)`. -/
abbrev CoordinateRing (p : ℕ) [Fact p.Prime] : Type :=
  MvPolynomial (Fin 2) (BaseField p) ⧸
    Ideal.span ({equation p} : Set (MvPolynomial (Fin 2) (BaseField p)))

/-- The spectrum of `𝔽_p(t)[x, y] / (y ^ 2 - x ^ p + t)`. -/
def scheme (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (CoordinateRing p))

/-- The canonical structure morphism from the cusp hypersurface to
`Spec(𝔽_p(t))`. -/
def toBase (p : ℕ) [Fact p.Prime] :
    scheme p ⟶ Spec (CommRingCat.of (BaseField p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (BaseField p) (CoordinateRing p)))

/-- The cusp hypersurface `y ^ 2 - x ^ p + t = 0` as a scheme over `𝔽_p(t)`. -/
def overBase (p : ℕ) [Fact p.Prime] :
    Over (Spec (CommRingCat.of (BaseField p))) :=
  Over.mk (toBase p)

/-- If `2 < p`, the coordinate ring of the cusp hypersurface is a domain. -/
theorem coordinateRing_isDomain (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    IsDomain (CoordinateRing p) := by
  let q : Polynomial (BaseField p) := InseparablePoint.polynomial p
  have hq : Irreducible q := InseparablePoint.polynomial_irreducible p
  let P : Ideal (Polynomial (BaseField p)) := Ideal.span {q}
  have hP : P.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).2 hq.prime
  let f : Polynomial (Polynomial (BaseField p)) := Polynomial.X ^ 2 - Polynomial.C q
  have hm : f.Monic := Polynomial.monic_X_pow_sub_C q (by decide)
  have hf : Irreducible f := by
    apply Polynomial.irreducible_of_eisenstein_criterion hP
    · rw [hm.leadingCoeff]
      simpa only [P, Ideal.mem_span_singleton] using hq.not_dvd_one
    · intro n hn
      have hn' : n < 2 := by simpa [f, Polynomial.degree_X_pow_sub_C] using hn
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;>
        simp [f, P]
    · simp [f, Polynomial.degree_X_pow_sub_C]
    · change f.coeff 0 ∉ Ideal.span {q} ^ 2
      rw [show f.coeff 0 = -q by simp [f], Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, dvd_neg]
      intro h
      have hd : q * q ∣ q * 1 := by simpa [pow_two] using h
      exact hq.not_dvd_one ((mul_dvd_mul_iff_left hq.ne_zero).1 hd)
    · exact hm.isPrimitive
  let e : MvPolynomial (Fin 2) (BaseField p) ≃ₐ[BaseField p]
      Polynomial (Polynomial (BaseField p)) :=
    ((MvPolynomial.renameEquiv (BaseField p) (Equiv.swap (0 : Fin 2) 1)).trans
      (MvPolynomial.finSuccEquiv (BaseField p) 1)).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv (BaseField p) (Fin 1)))
  have hx : e (MvPolynomial.X (0 : Fin 2)) = Polynomial.C Polynomial.X := by
    dsimp only [e]
    simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_X, Equiv.swap_apply_left]
    rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl, MvPolynomial.finSuccEquiv_X_succ]
    simp [MvPolynomial.uniqueAlgEquiv_apply]
  have hy : e (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by
    simp [e, MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_X_zero]
  have hc : e (MvPolynomial.C (RatFunc.X : BaseField p)) =
      Polynomial.C (Polynomial.C (RatFunc.X : BaseField p)) := by
    simp [e, MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply,
      MvPolynomial.uniqueAlgEquiv_apply]
  have he : e (equation p) = f := by
    dsimp only [equation, f, q, InseparablePoint.polynomial]
    rw [map_add, map_sub, map_pow, map_pow, hy, hx, hc, map_sub, map_pow]
    ring
  have heprime : Prime (equation p) :=
    (MulEquiv.prime_iff e).1 (he.symm ▸ hf.prime)
  exact (Ideal.Quotient.isDomain_iff_prime _).2
    ((Ideal.span_singleton_prime heprime.ne_zero).2 heprime)

/-- The canonical domain structure on the cusp coordinate ring in
characteristic greater than two. -/
instance instIsDomainCoordinateRing (p : ℕ) [Fact p.Prime] [Fact (2 < p)] :
    IsDomain (CoordinateRing p) :=
  coordinateRing_isDomain p (Fact.out : 2 < p)

/-- If `2 < p`, the cusp hypersurface is a variety over `𝔽_p(t)`. -/
theorem overBase_variety (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    Variety (overBase p) := by
  letI : IsDomain (CoordinateRing p) := coordinateRing_isDomain p hp
  exact variety_spec (BaseField p) (CoordinateRing p)

/-- The variety structure on the cusp hypersurface in characteristic greater
than two. -/
instance instVarietyOverBase (p : ℕ) [Fact p.Prime] [Fact (2 < p)] :
    Variety (overBase p) :=
  overBase_variety p (Fact.out : 2 < p)

/-- If `2 < p`, the cusp hypersurface is regular. -/
theorem scheme_regular (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    Scheme.Regular (scheme p) := sorry

/-- The canonical regular scheme structure on the cusp hypersurface in
characteristic greater than two. -/
instance instRegularScheme (p : ℕ) [Fact p.Prime] [Fact (2 < p)] :
    Scheme.Regular (scheme p) :=
  scheme_regular p (Fact.out : 2 < p)

/-- If `2 < p`, the cusp coordinate ring is geometrically reduced over
`𝔽_p(t)`. -/
theorem coordinateRing_isGeometricallyReduced (p : ℕ) [Fact p.Prime]
    (hp : 2 < p) :
    Algebra.IsGeometricallyReduced (BaseField p) (CoordinateRing p) := sorry

/-- The canonical geometrically reduced algebra structure on the cusp
coordinate ring in characteristic greater than two. -/
instance instIsGeometricallyReducedCoordinateRing
    (p : ℕ) [Fact p.Prime] [Fact (2 < p)] :
    Algebra.IsGeometricallyReduced (BaseField p) (CoordinateRing p) :=
  coordinateRing_isGeometricallyReduced p (Fact.out : 2 < p)

/-- If `2 < p`, the cusp hypersurface is geometrically reduced over `𝔽_p(t)`. -/
theorem overBase_geometricallyReduced (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    SchemeOverField.geometricallyReduced (overBase p) := by
  apply (SchemeOverField.geometricallyReduced_iff_morphismGeometricallyReduced (overBase p)).2
  exact SchemeOverField.geometricallyReduced_spec_iff_isGeometricallyReduced.2
    (coordinateRing_isGeometricallyReduced p hp)

/-- If `2 < p`, the cusp coordinate ring is not geometrically normal over
`𝔽_p(t)`. -/
theorem coordinateRing_not_isGeometricallyNormal (p : ℕ) [Fact p.Prime]
    (hp : 2 < p) :
    ¬ Algebra.IsGeometricallyNormal (BaseField p) (CoordinateRing p) := sorry

/-- If `2 < p`, the cusp hypersurface is not geometrically normal over
`𝔽_p(t)`. -/
theorem overBase_not_geometricallyNormal (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    ¬ SchemeOverField.geometricallyNormal (overBase p) := by
  intro h
  exact coordinateRing_not_isGeometricallyNormal p hp
    (isGeometricallyNormal_of_geometricallyNormal_spec (BaseField p) (CoordinateRing p) h)

end Cusp

end AlgebraicGeometry.RationalFunctionRegularityCounterexample
