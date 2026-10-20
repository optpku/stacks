/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.TripleEulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.OverSpec
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.RingTheory.Depth

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.CoherentTriple

/-- The comparison isomorphism on the punctured closed fiber induces the canonical
linear restriction map from sections on the punctured spectrum. -/
noncomputable def globalSectionsRestriction (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules),
      (α : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      Scheme.Hom.globalSectionsMod S.U.ι L ⟶
        Scheme.Hom.globalSectionsMod ((S.y ∣_ S.U) ≫ S.U.ι) (L₀.restrict U₀.ι) :=
  let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
    (IsLocalRing.maximalIdeal A)
    ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
  fun L L₀ α =>
    (globalSectionsPullbackLinear S.U.ι (S.y ∣_ S.U) L) ≫
      (Scheme.Hom.globalSectionsFunctor
        ((S.y ∣_ S.U) ≫ S.U.ι)).map α.hom

/-- Restriction on global sections is pullback followed by the map on sections of the
closed-fiber comparison isomorphism. -/
theorem globalSectionsRestriction_def (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules),
      (α : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      globalSectionsRestriction A f hf_mem L L₀ α =
      (globalSectionsPullbackLinear S.U.ι (S.y ∣_ S.U) L) ≫
        (Scheme.Hom.globalSectionsFunctor
          ((S.y ∣_ S.U) ≫ S.U.ι)).map α.hom :=
  fun L L₀ α => rfl

/-- Under depth at least three, an invertible coherent triple has a finite-length
cokernel of restriction on global sections. -/
theorem globalSectionsRestriction_cokernel_finiteLength (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [L.IsCoherent] [L₀.IsCoherent]
      [Invertible L] [Invertible L₀],
      (hL : ∀ V : S.U.toScheme.Opens, Function.Injective
        (L.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      IsFiniteLength A
        (Scheme.Hom.globalSectionsMod ((S.y ∣_ S.U) ≫ S.U.ι)
            (L₀.restrict U₀.ι) ⧸
          LinearMap.range (globalSectionsRestriction A f hf_mem L L₀ α).hom) := sorry

/-- Under depth at least three, the intrinsic Euler characteristic of an invertible
coherent triple equals the length of the cokernel of restriction on global sections. -/
theorem eulerCharacteristic_eq_cokernelLength (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [L.IsCoherent] [L₀.IsCoherent]
      [Invertible L] [Invertible L₀],
      (hL : ∀ V : S.U.toScheme.Opens, Function.Injective
        (L.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      eulerCharacteristic A f hf_mem L L₀ hL α =
        ((Module.length A
          (Scheme.Hom.globalSectionsMod ((S.y ∣_ S.U) ≫ S.U.ι)
            (L₀.restrict U₀.ι) ⧸
          LinearMap.range (globalSectionsRestriction A f hf_mem L L₀ α).hom)).toNat : ℤ) := sorry

/-- The intrinsic Euler characteristic of an invertible coherent triple is nonnegative
when the local ring has depth at least three. -/
theorem eulerCharacteristic_nonneg (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [L.IsCoherent] [L₀.IsCoherent]
      [Invertible L] [Invertible L₀],
      (hL : ∀ V : S.U.toScheme.Opens, Function.Injective
        (L.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      0 ≤ eulerCharacteristic A f hf_mem L L₀ hL α := sorry

/-- Over a local ring of depth at least three, an invertible coherent triple has zero
intrinsic Euler characteristic exactly when its punctured component is trivial. -/
theorem eulerCharacteristic_eq_zero_iff_isoUnit (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [L.IsCoherent] [L₀.IsCoherent]
      [Invertible L] [Invertible L₀],
      (hL : ∀ V : S.U.toScheme.Opens, Function.Injective
        (L.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      eulerCharacteristic A f hf_mem L L₀ hL α = 0 ↔
        Nonempty (L ≅
          (SheafOfModules.unit S.U.toScheme.ringCatSheaf : S.U.toScheme.Modules)) := sorry

end AlgebraicGeometry.Scheme.Modules.CoherentTriple
