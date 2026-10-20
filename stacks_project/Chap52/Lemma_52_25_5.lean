module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.TripleEulerCharacteristic.Invertible
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 52.25.5: the Euler characteristic of an invertible coherent triple is the
cokernel length of restriction on sections, is nonnegative, and vanishes exactly when
the punctured component is trivial. -/
@[stacks 0F28]
#check (AlgebraicGeometry.Scheme.Modules.CoherentTriple.eulerCharacteristic_eq_cokernelLength :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
      (hf_regular : IsRegular f) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A),
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [L.IsCoherent] [L₀.IsCoherent]
      [Scheme.Modules.Invertible L] [Scheme.Modules.Invertible L₀],
      (hL : ∀ V : S.U.toScheme.Opens, Function.Injective
        (L.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (Scheme.Modules.pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      AlgebraicGeometry.Scheme.Modules.CoherentTriple.eulerCharacteristic A f hf_mem L L₀ hL α =
        ((Module.length A
          (Scheme.Hom.globalSectionsMod ((S.y ∣_ S.U) ≫ S.U.ι)
            (L₀.restrict U₀.ι) ⧸
          LinearMap.range (AlgebraicGeometry.Scheme.Modules.CoherentTriple.globalSectionsRestriction A f hf_mem L L₀ α).hom)).toNat : ℤ))

#check (AlgebraicGeometry.Scheme.Modules.CoherentTriple.eulerCharacteristic_nonneg :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
      (hf_regular : IsRegular f) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A),
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [L.IsCoherent] [L₀.IsCoherent]
      [Scheme.Modules.Invertible L] [Scheme.Modules.Invertible L₀],
      (hL : ∀ V : S.U.toScheme.Opens, Function.Injective
        (L.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (Scheme.Modules.pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      0 ≤ AlgebraicGeometry.Scheme.Modules.CoherentTriple.eulerCharacteristic A f hf_mem L L₀ hL α)

#check (AlgebraicGeometry.Scheme.Modules.CoherentTriple.eulerCharacteristic_eq_zero_iff_isoUnit :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
      (hf_regular : IsRegular f) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A),
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [L.IsCoherent] [L₀.IsCoherent]
      [Scheme.Modules.Invertible L] [Scheme.Modules.Invertible L₀],
      (hL : ∀ V : S.U.toScheme.Opens, Function.Injective
        (L.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (Scheme.Modules.pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      AlgebraicGeometry.Scheme.Modules.CoherentTriple.eulerCharacteristic A f hf_mem L L₀ hL α = 0 ↔
        Nonempty (L ≅
          (SheafOfModules.unit S.U.toScheme.ringCatSheaf : S.U.toScheme.Modules)))

