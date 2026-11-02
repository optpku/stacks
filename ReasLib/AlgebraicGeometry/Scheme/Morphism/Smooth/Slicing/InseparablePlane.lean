/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Fiber
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Spectrum.Maximal.Topology

/-!
# An inseparable point of the affine plane

This file constructs a closed point on a positive-dimensional fibre of the
smooth affine-plane projection which admits no compatible lift from a scheme
étale over the affine line.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.InseparablePlanePoint

variable (p : ℕ) [Fact p.Prime]

/-- The ideal `(x, y ^ p - a)` defining the distinguished affine-plane point. -/
def pointIdeal (k : Type u) [Field k] (a : k) :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X (0 : Fin 2),
    MvPolynomial.X (1 : Fin 2) ^ p - MvPolynomial.C a}

/-- The distinguished ideal is the span of `x` and `y ^ p - a`. -/
theorem pointIdeal_eq_span (k : Type u) [Field k] (a : k) :
    pointIdeal p k a =
      Ideal.span {MvPolynomial.X (0 : Fin 2),
        MvPolynomial.X (1 : Fin 2) ^ p - MvPolynomial.C a} := rfl

/-- If `a` is not a `p`-th power, the ideal `(x, y ^ p - a)` is maximal. -/
theorem pointIdeal_isMaximal (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    (pointIdeal p k a).IsMaximal := by
  let e : MvPolynomial (Fin 2) k ≃+* Polynomial (Polynomial k) :=
    (MvPolynomial.finSuccEquiv k 1).toRingEquiv.trans
      (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv)
  have he₀ : e (MvPolynomial.X 0) = Polynomial.X := by
    simp [e, MvPolynomial.finSuccEquiv_X_zero]
  have he₁ : e (MvPolynomial.X 1) = Polynomial.C Polynomial.X := by
    change Polynomial.map (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingHom
      ((MvPolynomial.finSuccEquiv k 1) (MvPolynomial.X (0 : Fin 1).succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    simp [MvPolynomial.uniqueAlgEquiv]
  have heC (b : k) : e (MvPolynomial.C b) = Polynomial.C (Polynomial.C b) := by
    simp [e, MvPolynomial.finSuccEquiv_apply]
  let f : MvPolynomial (Fin 2) k →+* Polynomial k :=
    Polynomial.constantCoeff.comp e.toRingHom
  have hf : Function.Surjective f := by
    intro q
    refine ⟨e.symm (Polynomial.C q), ?_⟩
    simp [f]
  have hk : RingHom.ker f ≤ pointIdeal p k a := by
    intro q hq
    change (e q).coeff 0 = 0 at hq
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.2 hq
    have hq' : q = MvPolynomial.X 0 * e.symm r := by
      apply e.injective
      rw [map_mul, he₀, e.apply_symm_apply]
      exact hr
    rw [hq']
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  have hmap : Ideal.map f (pointIdeal p k a) =
      Ideal.span {Polynomial.X ^ p - Polynomial.C a} := by
    simp only [pointIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      map_sub, map_pow]
    change Ideal.span {Polynomial.constantCoeff (e (MvPolynomial.X 0)),
      Polynomial.constantCoeff (e (MvPolynomial.X 1)) ^ p -
        Polynomial.constantCoeff (e (MvPolynomial.C a))} = _
    simp [he₀, he₁, heC]
  letI : (Ideal.span {Polynomial.X ^ p - Polynomial.C a}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime)
        (fun b hb ↦ ha ⟨b, hb⟩))
  haveI : (Ideal.map f (pointIdeal p k a)).IsMaximal := hmap.symm ▸ inferInstance
  have hm := Ideal.comap_isMaximal_of_surjective f hf
    (K := Ideal.map f (pointIdeal p k a))
  rwa [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
    sup_of_le_left hk] at hm

/-- The maximal-spectrum point represented by `(x, y ^ p - a)`. -/
def point (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    MaximalSpectrum (MvPolynomial (Fin 2) k) :=
  ⟨pointIdeal p k a, pointIdeal_isMaximal p k a ha⟩

/-- The ideal underlying the distinguished maximal-spectrum point. -/
theorem point_asIdeal (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    (point p k a ha).asIdeal = pointIdeal p k a := rfl

/-- The coordinate-ring map `k[x] → k[x, y]` sending `x` to the first coordinate. -/
def projectionRingHom (k : Type u) [Field k] :
    Polynomial k →+* MvPolynomial (Fin 2) k :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0 : Fin 2))

/-- The coordinate-ring map sends `Polynomial.X` to the first plane coordinate. -/
theorem projectionRingHom_X (k : Type u) [Field k] :
    projectionRingHom k Polynomial.X = MvPolynomial.X (0 : Fin 2) := by
  simp [projectionRingHom]

/-- The affine-plane projection induced by `k[x] → k[x, y]`. -/
def projection (k : Type u) [Field k] :
    Spec (CommRingCat.of (MvPolynomial (Fin 2) k)) ⟶
      Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (projectionRingHom k))

/-- The projection acts on points by contraction along `projectionRingHom`. -/
theorem projection_apply (k : Type u) [Field k]
    (x : PrimeSpectrum (MvPolynomial (Fin 2) k)) :
    projection k x = PrimeSpectrum.comap (projectionRingHom k) x := rfl

/-- The affine-plane projection is smooth. -/
instance projection_smooth (k : Type u) [Field k] : Smooth (projection k) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
  let e : MvPolynomial (Fin 2) k ≃+* Polynomial (Polynomial k) :=
    ((MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1)).trans
      (MvPolynomial.finSuccEquiv k 1)).toRingEquiv.trans
        (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv)
  have he : e.toRingHom.comp (projectionRingHom k) = Polynomial.C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [e, projectionRingHom, MvPolynomial.finSuccEquiv_apply]
    · change e (projectionRingHom k Polynomial.X) = Polynomial.C Polynomial.X
      rw [projectionRingHom_X]
      change Polynomial.map (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingHom
          ((MvPolynomial.finSuccEquiv k 1)
            ((MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1))
              (MvPolynomial.X 0))) = Polynomial.C Polynomial.X
      simp only [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
        Equiv.swap_apply_left]
      change Polynomial.map (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingHom
        ((MvPolynomial.finSuccEquiv k 1) (MvPolynomial.X (0 : Fin 1).succ)) = _
      rw [MvPolynomial.finSuccEquiv_X_succ]
      simp [MvPolynomial.uniqueAlgEquiv]
  have hs : (e.toRingHom.comp (projectionRingHom k)).Smooth := by
    rw [he]
    exact (RingHom.smooth_algebraMap (R := Polynomial k)
      (S := Polynomial (Polynomial k))).2 ⟨inferInstance, inferInstance⟩
  have hcancel : e.symm.toRingHom.comp (e.toRingHom.comp (projectionRingHom k)) =
      projectionRingHom k := by
    apply RingHom.ext
    intro f
    exact e.symm_apply_apply _
  exact hcancel ▸ RingHom.Smooth.respectsIso.1 _ e.symm hs

/-- The residue-field map at the distinguished point is purely inseparable. -/
theorem pointResidueFieldMap_isPurelyInseparable
    (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    ((projection k).residueFieldMap
      (point p k a ha).toPrimeSpectrum).hom.IsPurelyInseparable := sorry

/-- The residue field at the distinguished point is not separable over that of its image. -/
theorem pointResidueField_notSeparable
    (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    ¬ Algebra.IsSeparable
      ((Spec (CommRingCat.of (Polynomial k))).residueField
        (projection k (point p k a ha).toPrimeSpectrum))
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).residueField
        (point p k a ha).toPrimeSpectrum) := sorry

/-- The point `(x, y ^ p - a)` is closed in the affine plane. -/
theorem point_mem_closedPoints
    (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    (point p k a ha).toPrimeSpectrum ∈
      closedPoints (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))) := by
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (point p k a ha).isMaximal

/-- The distinguished point lies on a positive-dimensional fibre. -/
theorem fiberDimensionAt_pos
    (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    0 < (projection k).fiberDimensionAt
      (point p k a ha).toPrimeSpectrum := sorry

/-- The distinguished point is not in the image of a morphism from an étale scheme over the
affine line that is compatible with the affine-plane projection. -/
@[stacks 057E]
theorem noEtaleLift
    (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    ¬ ∃ (S' : Scheme.{u})
        (g : S' ⟶ Spec (CommRingCat.of (Polynomial k)))
        (h : S' ⟶ Spec (CommRingCat.of (MvPolynomial (Fin 2) k))),
      Etale g ∧ h ≫ projection k = g ∧
        (point p k a ha).toPrimeSpectrum ∈ Set.range h := by
  rintro ⟨S', g, h, hg, hcomm, x, hx⟩
  letI : Etale (h ≫ projection k) := hcomm.symm ▸ hg
  letI : FormallyUnramified (h ≫ projection k) :=
    { formallyUnramified_appLE := fun {_} hU {_} hV e ↦
        ((h ≫ projection k).etale_appLE hU hV e).formallyUnramified }
  letI : LocallyOfFiniteType (h ≫ projection k) :=
    { finiteType_appLE := fun {_} hU {_} hV e ↦
        RingHom.FiniteType.of_finitePresentation
          (RingHom.Etale.iff_flat_and_formallyUnramified.mp
            ((h ≫ projection k).etale_appLE hU hV e)).2.2 }
  letI : Algebra
      ((Spec (CommRingCat.of (Polynomial k))).residueField (projection k (h x)))
      (S'.residueField x) := ((h ≫ projection k).residueFieldMap x).hom.toAlgebra
  haveI : Algebra.IsSeparable
      ((Spec (CommRingCat.of (Polynomial k))).residueField (projection k (h x)))
      (S'.residueField x) :=
    FormallyUnramified.instIsSeparableCarrierResidueFieldCoeContinuousMapCarrierCarrierCommRingCatHomTopCatBaseOfLocallyOfFiniteType
      (h ≫ projection k) x
  let φ :
      (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).residueField (h x) →ₐ[
        (Spec (CommRingCat.of (Polynomial k))).residueField (projection k (h x))]
        S'.residueField x :=
    { (h.residueFieldMap x).hom with
      commutes' := fun r ↦ by
        change ((h.residueFieldMap x).hom.comp
          ((projection k).residueFieldMap (h x)).hom) r =
            ((h ≫ projection k).residueFieldMap x).hom r
        rw [Scheme.residueFieldMap_comp]
        rfl }
  have hsep := Algebra.IsSeparable.of_algHom _ _ φ
  exact pointResidueField_notSeparable p k a ha (hx ▸ hsep)

end AlgebraicGeometry.InseparablePlanePoint
