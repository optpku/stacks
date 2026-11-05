/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import ReasLib.RingTheory.Extension.SquareZero

/-!
# Localization of square-zero algebra extensions

Localization along the inverse image of a multiplicative subset induces a map
on square-zero extensions with specified coefficients and on their classes.
-/

@[expose] public section
noncomputable section
universe u

open Algebra

namespace Algebra.SquareZeroAlgExtension

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- The inverse image of a multiplicative subset under an extension projection. -/
abbrev localizationSubmonoid (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
    @Submonoid e.carrier e.commRing.toMonoid.toMulOneClass :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  S.comap e.toB.toRingHom

/-- The inverse-image submonoid has the expected underlying set. -/
theorem localizationSubmonoid_eq_comap (e : SquareZeroAlgExtension A B N)
    (S : Submonoid B) :
    (localizationSubmonoid e S : Set e.carrier) = e.toB ⁻¹' (S : Set B) := rfl

/-- Membership in the inverse-image submonoid is membership of the projection. -/
theorem mem_localizationSubmonoid (e : SquareZeroAlgExtension A B N) (S : Submonoid B)
    {x : e.carrier} :
    x ∈ localizationSubmonoid e S ↔ e.toB x ∈ S := Iff.rfl

private def localize_projectionRing (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  Localization (localizationSubmonoid e S) →+* Localization S :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  IsLocalization.map (Localization S) e.toB.toRingHom
    (le_rfl : localizationSubmonoid e S ≤ S.comap e.toB.toRingHom)

private theorem localize_projection_commutes (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  ∀ a : A,
    localize_projectionRing e S (algebraMap A (Localization (localizationSubmonoid e S)) a) =
      algebraMap A (Localization S) a := by
  letI := e.commRing
  letI := e.algebra
  intro a
  change localize_projectionRing e S
    (algebraMap e.carrier (Localization (localizationSubmonoid e S))
      (algebraMap A e.carrier a)) = _
  rw [localize_projectionRing, IsLocalization.map_eq]
  change (algebraMap B (Localization S)) (e.toB (algebraMap A e.carrier a)) = _
  rw [e.toB.commutes]
  rfl

private def localize_projection (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  Localization (localizationSubmonoid e S) →ₐ[A] Localization S :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  { toRingHom := localize_projectionRing e S
    commutes' := localize_projection_commutes e S }

private theorem localize_projection_isSquareZero (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack the stored square-zero projection.
  letI := e.isSquareZero
  (localize_projection e S).toRingHom.IsSquareZeroExtension := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  have hS : (localizationSubmonoid e S).map e.toB.toRingHom = S :=
    Submonoid.map_comap_eq_self_of_surjective e.isSquareZero.surjective
  constructor
  · letI : IsLocalization ((localizationSubmonoid e S).map e.toB.toRingHom)
        (Localization S) := hS.symm ▸ inferInstance
    exact IsLocalization.map_surjective_of_surjective
      (localizationSubmonoid e S) (Localization (localizationSubmonoid e S))
      (Localization S) (g := e.toB.toRingHom) e.isSquareZero.surjective
  · have hk := IsLocalization.ker_map (S := Localization (localizationSubmonoid e S))
      (Localization S) e.toB.toRingHom hS
    change RingHom.ker (localize_projection e S).toRingHom = _ at hk
    rw [hk, ← Ideal.map_pow, e.isSquareZero.ker_sq_eq_bot, Ideal.map_bot]

private theorem localize_kernelFraction_wellDefined (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  ∀ p p' : RingHom.ker e.toB.toRingHom × localizationSubmonoid e S,
    p ≈ p' → Localization.mk p.1.1 p.2 = Localization.mk p'.1.1 p'.2 := by
  letI := e.commRing
  letI := e.algebra
  intro p p' h
  obtain ⟨u, hu⟩ := h
  exact Localization.mk_eq_mk_iff.mpr <| Localization.r_iff_exists.mpr
    ⟨u, congrArg Subtype.val hu⟩

private def localize_kernelFraction (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  LocalizedModule (localizationSubmonoid e S) (RingHom.ker e.toB.toRingHom) →
    Localization (localizationSubmonoid e S) :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  fun z ↦ LocalizedModule.liftOn z
    (fun p ↦ Localization.mk p.1.1 p.2)
    (localize_kernelFraction_wellDefined e S)

private theorem localize_kernelMap_mem (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  ∀ z, localize_kernelFraction e S z ∈ RingHom.ker (localize_projection e S).toRingHom := by
  letI := e.commRing
  letI := e.algebra
  intro z
  induction z using LocalizedModule.induction_on with
  | _ x s =>
    change localize_projectionRing e S (localize_kernelFraction e S (.mk x s)) = 0
    simp only [localize_kernelFraction, LocalizedModule.liftOn_mk,
      localize_projectionRing, Localization.mk_eq_mk', IsLocalization.map_mk']
    have hx : e.toB.toRingHom x.val = 0 := x.property
    rw [hx, IsLocalization.mk'_zero]

private def localize_kernelMap (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  LocalizedModule (localizationSubmonoid e S) (RingHom.ker e.toB.toRingHom) →
    RingHom.ker (localize_projection e S).toRingHom :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  fun z ↦ ⟨localize_kernelFraction e S z, localize_kernelMap_mem e S z⟩

private theorem localize_kernelMap_bijective (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  Function.Bijective (localize_kernelMap e S) := by
  letI := e.commRing
  letI := e.algebra
  constructor
  · intro z z' h
    induction z, z' using LocalizedModule.induction_on₂ with
    | _ x y s t =>
      have h' : Localization.mk x.val s = Localization.mk y.val t :=
        congrArg Subtype.val h
      obtain ⟨u, hu⟩ := Localization.r_iff_exists.mp (Localization.mk_eq_mk_iff.mp h')
      exact LocalizedModule.mk_eq.mpr ⟨u, Subtype.ext hu⟩
  · rintro ⟨x, hx⟩
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (localizationSubmonoid e S) x
    change localize_projectionRing e S (IsLocalization.mk' _ r s) = 0 at hx
    rw [localize_projectionRing, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨c, hc⟩ := e.isSquareZero.surjective t.val
    change e.toB c = t.val at hc
    let cS : localizationSubmonoid e S := ⟨c, by change e.toB c ∈ S; rw [hc]; exact t.property⟩
    let y : RingHom.ker e.toB.toRingHom := ⟨c * r, by
      change e.toB (c * r) = 0
      rw [map_mul, hc]
      exact ht⟩
    refine ⟨LocalizedModule.mk y (cS * s), Subtype.ext ?_⟩
    change Localization.mk (c * r) (cS * s) = IsLocalization.mk' _ r s
    rw [← Localization.mk_eq_mk']
    apply Localization.mk_eq_mk_iff.mpr
    apply Localization.r_iff_exists.mpr
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul]
    change s.val * (c * r) = (c * s.val) * r
    ring

private theorem localize_toCotangent_smul (e : SquareZeroAlgExtension A B N) :
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  ∀ (r : e.carrier) (x : RingHom.ker e.toB.toRingHom),
    RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom (r • x) =
      e.toB r • RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom x := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  intro r x
  change Ideal.toCotangent _ (r • x) = e.toB r • Ideal.toCotangent _ x
  rw [map_smul]
  change r • Ideal.toCotangent _ x =
    (e.toB.toRingHom.quotientKerEquivOfSurjective e.isSquareZero.surjective).symm
      (e.toB.toRingHom r) • Ideal.toCotangent _ x
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  exact (IsScalarTower.algebraMap_smul
    (e.carrier ⧸ RingHom.ker e.toB.toRingHom) r (Ideal.toCotangent _ x)).symm

private theorem localize_cotangentFraction_wellDefined (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack the stored square-zero projection.
  letI := e.isSquareZero
  ∀ p p' : RingHom.ker e.toB.toRingHom × localizationSubmonoid e S,
    p ≈ p' →
      LocalizedModule.mk
        (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom p.1)
        (⟨e.toB p.2, p.2.property⟩ : S) =
      LocalizedModule.mk
        (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom p'.1)
        (⟨e.toB p'.2, p'.2.property⟩ : S) := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  intro p p' h
  obtain ⟨u, hu⟩ := h
  refine LocalizedModule.mk_eq.mpr ⟨⟨e.toB u, u.property⟩, ?_⟩
  simpa only [Submonoid.smul_def, localize_toCotangent_smul] using
    congrArg (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom) hu

private def localize_cotangentFraction (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack the stored square-zero projection.
  letI := e.isSquareZero
  LocalizedModule (localizationSubmonoid e S) (RingHom.ker e.toB.toRingHom) →
    LocalizedModule S (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)) :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack the stored square-zero projection.
  letI := e.isSquareZero
  fun z ↦ LocalizedModule.liftOn z
    (fun p ↦ LocalizedModule.mk
      (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom p.1)
      (⟨e.toB p.2, p.2.property⟩ : S))
    (localize_cotangentFraction_wellDefined e S)

private theorem localize_cotangentFraction_bijective
    (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  Function.Bijective (localize_cotangentFraction e S) := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  constructor
  · intro z z' h
    induction z, z' using LocalizedModule.induction_on₂ with
    | _ x y s t =>
      change LocalizedModule.mk
        (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom x)
        (⟨e.toB s, s.property⟩ : S) =
        LocalizedModule.mk
        (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom y)
        (⟨e.toB t, t.property⟩ : S) at h
      obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h
      obtain ⟨c, hc⟩ := e.isSquareZero.surjective u.val
      change e.toB c = u.val at hc
      let cS : localizationSubmonoid e S :=
        ⟨c, by change e.toB c ∈ S; rw [hc]; exact u.property⟩
      refine LocalizedModule.mk_eq.mpr ⟨cS, ?_⟩
      apply (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom).injective
      simpa only [Submonoid.smul_def, localize_toCotangent_smul, cS, hc] using hu
  · intro z
    induction z using LocalizedModule.induction_on with
    | _ x s =>
      obtain ⟨c, hc⟩ := e.isSquareZero.surjective s.val
      change e.toB c = s.val at hc
      let cS : localizationSubmonoid e S :=
        ⟨c, by change e.toB c ∈ S; rw [hc]; exact s.property⟩
      refine ⟨LocalizedModule.mk
        ((RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom).symm x) cS, ?_⟩
      change LocalizedModule.mk
        ((RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom)
          ((RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom).symm x))
        (⟨e.toB c, cS.property⟩ : S) = LocalizedModule.mk x s
      rw [LinearEquiv.apply_symm_apply]
      congr 1
      exact Subtype.ext hc

private def localize_kernelValue (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack the stored square-zero projection.
  letI := e.isSquareZero
  -- Local instance justification (proof-local temporary data): use the proved square-zero property of the localized projection.
  letI := localize_projection_isSquareZero e S
  Ideal.Cotangent (RingHom.ker (localize_projection e S).toRingHom) →
    LocalizedModule S N :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack the stored square-zero projection.
  letI := e.isSquareZero
  -- Local instance justification (proof-local temporary data): use the proved square-zero property of the localized projection.
  letI := localize_projection_isSquareZero e S
  fun x ↦
    let xKer :=
      (RingHom.SquareZeroExtension.toCotangentEquiv_source
        (localize_projection e S).toRingHom).symm x
    let z := (Equiv.ofBijective (localize_kernelMap e S)
      (localize_kernelMap_bijective e S)).symm xKer
    LocalizedModule.map S e.kernelEquiv.toLinearMap (localize_cotangentFraction e S z)

private theorem localize_kernelValue_add (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack the stored square-zero projection.
  letI := e.isSquareZero
  -- Local instance justification (proof-local temporary data): use the proved square-zero property of the localized projection.
  letI := localize_projection_isSquareZero e S
  ∀ x y, localize_kernelValue e S (x + y) =
    localize_kernelValue e S x + localize_kernelValue e S y := sorry

private theorem localize_kernelValue_smul (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack the stored square-zero projection.
  letI := e.isSquareZero
  -- Local instance justification (proof-local temporary data): use the proved square-zero property of the localized projection.
  letI := localize_projection_isSquareZero e S
  ∀ (r : Localization S) x, localize_kernelValue e S (r • x) =
    r • localize_kernelValue e S x := sorry

private theorem localize_kernelValue_bijective (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack the stored square-zero projection.
  letI := e.isSquareZero
  -- Local instance justification (proof-local temporary data): use the proved square-zero property of the localized projection.
  letI := localize_projection_isSquareZero e S
  Function.Bijective (localize_kernelValue e S) := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  letI := localize_projection_isSquareZero e S
  exact (show Function.Bijective (LocalizedModule.map S e.kernelEquiv.toLinearMap) from
    ⟨LocalizedModule.map_injective S _ e.kernelEquiv.injective,
      LocalizedModule.map_surjective S _ e.kernelEquiv.surjective⟩).comp
    ((localize_cotangentFraction_bijective e S).comp
      ((Equiv.ofBijective (localize_kernelMap e S)
        (localize_kernelMap_bijective e S)).symm.bijective.comp
        (RingHom.SquareZeroExtension.toCotangentEquiv_source
          (localize_projection e S).toRingHom).symm.bijective))

/-- Localization of a square-zero extension along the inverse image of a multiplicative subset,
with the induced localization of its specified coefficient identification. -/
def localize (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
    SquareZeroAlgExtension A (Localization S) (LocalizedModule S N) :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack the stored square-zero projection.
  letI := e.isSquareZero
  let S_C := localizationSubmonoid e S
  let toB' : Localization S_C →ₐ[A] Localization S :=
    { toRingHom := IsLocalization.map (Localization S) e.toB.toRingHom
        (le_rfl : S_C ≤ S.comap e.toB.toRingHom)
      commutes' := by exact localize_projection_commutes e S }
  -- Local instance justification (proof-local temporary data): use the proved square-zero property of the localized projection.
  letI : toB'.toRingHom.IsSquareZeroExtension := by exact localize_projection_isSquareZero e S
  let kernelMap : LocalizedModule S_C (RingHom.ker e.toB.toRingHom) →
      RingHom.ker toB'.toRingHom :=
    fun z ↦ ⟨LocalizedModule.liftOn z (fun p ↦ Localization.mk p.1.1 p.2)
      (by exact localize_kernelFraction_wellDefined e S), by exact localize_kernelMap_mem e S z⟩
  let kernelEquiv := Equiv.ofBijective kernelMap (by exact localize_kernelMap_bijective e S)
  of toB' (LinearEquiv.ofBijective
    { toFun := fun x ↦
        let xKer :=
          (RingHom.SquareZeroExtension.toCotangentEquiv_source toB'.toRingHom).symm x
        let z := kernelEquiv.symm xKer
        let zCot := LocalizedModule.liftOn z
          (fun p ↦ LocalizedModule.mk
            (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom p.1)
            (⟨e.toB p.2, p.2.property⟩ : S))
          (by exact localize_cotangentFraction_wellDefined e S)
        LocalizedModule.map S e.kernelEquiv.toLinearMap zCot
      map_add' := by exact localize_kernelValue_add e S
      map_smul' := by exact localize_kernelValue_smul e S }
    (by exact localize_kernelValue_bijective e S))

end Algebra.SquareZeroAlgExtension

namespace Algebra.Exal

variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

private theorem localize_respects (S : Submonoid B)
    (f g : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (h : mk A B N f = mk A B N g) :
    SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).localize S) =
      SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom g).localize S) := sorry

/-- The map on first-order extension classes induced by localization. -/
def localize (S : Submonoid B) :
    Exal A B N → Exal A (Localization S) (LocalizedModule S N) :=
  fun x ↦ Quotient.liftOn x
    (fun f ↦ SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).localize S))
    (fun f g h ↦ by exact localize_respects A B N S f g (Quotient.sound h))

/-- The localization of a conormal-map class is represented by the localized geometric extension. -/
theorem localize_mk (S : Submonoid B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    localize A B N S (mk A B N f) =
      SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).localize S) := rfl

/-- Localization on extension classes agrees with localization of every geometric representative. -/
theorem localize_toClass (S : Submonoid B) (e : SquareZeroAlgExtension A B N) :
    localize A B N S (SquareZeroAlgExtension.toClass e) =
      SquareZeroAlgExtension.toClass (e.localize S) := sorry

/-- For a finite type algebra over a field and finite coefficients, localization away from every
nonsmooth prime induces a bijection on first-order extension classes. -/
theorem localize_bijective (k B N : Type u) [Field k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N] [Algebra.FiniteType k B] [Module.Finite B N]
    (S : Submonoid B)
    (hS : ∀ q : PrimeSpectrum B, q ∉ smoothLocus k B →
      (S : Set B) ∩ q.asIdeal = ∅) :
    Function.Bijective (localize k B N S) := sorry

end Algebra.Exal
