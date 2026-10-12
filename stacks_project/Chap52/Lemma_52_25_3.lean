/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.TripleEulerCharacteristic
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.CoherentTriple CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

/- Lemma 52.25.3: the Euler characteristic is additive along a short exact sequence of
coherent triples. -/
@[stacks 0F26] #check
  (AlgebraicGeometry.Scheme.Modules.CoherentTriple.eulerCharacteristic_eq_add_of_shortExact :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) (hf_regular : IsRegular f),
      let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
        (IsLocalRing.maximalIdeal A)
        ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
      let U₀ := S.y ⁻¹ᵁ S.U
      ∀ (E : CategoryTheory.ShortComplex S.U.toScheme.Modules)
        (E₀ : CategoryTheory.ShortComplex S.Y.Modules)
        [E.X₁.IsCoherent] [E.X₂.IsCoherent] [E.X₃.IsCoherent]
        [E₀.X₁.IsCoherent] [E₀.X₂.IsCoherent] [E₀.X₃.IsCoherent],
        (h₁ : ∀ V : S.U.toScheme.Opens, Function.Injective
          (E.X₁.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
        (h₂ : ∀ V : S.U.toScheme.Opens, Function.Injective
          (E.X₂.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
        (h₃ : ∀ V : S.U.toScheme.Opens, Function.Injective
          (E.X₃.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
        (α₁ : (pullback (S.y ∣_ S.U)).obj E.X₁ ≅ E₀.X₁.restrict U₀.ι) →
        (α₂ : (pullback (S.y ∣_ S.U)).obj E.X₂ ≅ E₀.X₂.restrict U₀.ι) →
        (α₃ : (pullback (S.y ∣_ S.U)).obj E.X₃ ≅ E₀.X₃.restrict U₀.ι) →
        (pullback (S.y ∣_ S.U)).map E.f ≫ α₂.hom =
            α₁.hom ≫ (restrictFunctor U₀.ι).map E₀.f →
        (pullback (S.y ∣_ S.U)).map E.g ≫ α₃.hom =
            α₂.hom ≫ (restrictFunctor U₀.ι).map E₀.g →
        E.ShortExact → E₀.ShortExact →
        eulerCharacteristic A f hf_mem E.X₂ E₀.X₂ h₂ α₂ =
          eulerCharacteristic A f hf_mem E.X₁ E₀.X₁ h₁ α₁ +
            eulerCharacteristic A f hf_mem E.X₃ E₀.X₃ h₃ α₃)
