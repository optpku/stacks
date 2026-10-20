module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.TripleHilbertPolynomial

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Proposition 52.25.4: The Euler characteristic of the integral twists of a coherent triple
by an invertible coherent triple is a polynomial, constant when the punctured support is empty. -/
@[stacks 0F27] #check
  (AlgebraicGeometry.Scheme.Modules.CoherentTriple.eulerCharacteristic_tensorPower_degreeLE :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) (hf_regular : IsRegular f),
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules)
      (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules)
      [F.IsCoherent] [F₀.IsCoherent] [L.IsCoherent] [L₀.IsCoherent]
      [Invertible L] [Invertible L₀],
      (hF : ∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (hL : ∀ V : S.U.toScheme.Opens, Function.Injective
        (L.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι) →
      (eL : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      ∃ p : Polynomial ℚ,
        (∀ n : ℤ, p.eval (n : ℚ) =
          (AlgebraicGeometry.Scheme.Modules.CoherentTriple.twistEulerCharacteristic A f hf_mem F F₀ L L₀ hF α eL n : ℚ)) ∧
        (p.natDegree : WithBot ℕ∞) ≤
          max 0 (topologicalKrullDim (moduleSupport F)))
