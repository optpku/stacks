module

public import ReasLib.AlgebraicGeometry.Hilbert.AddPoint
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.SmoothCurve

/-!
# Addition of relative effective divisors

This file constructs the pointwise addition transformation for Hilbert functors of arbitrary
degrees and the induced morphism between their representing schemes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Hilbert

variable {S : Scheme.{u}}

namespace Point

/-- A Hilbert point on a smooth relative curve is a relative effective Cartier divisor. -/
theorem ideal_isRelativeEffectiveCartierDivisor
    {X T : Over S} [SmoothOfRelativeDimension 1 X.hom] {d : ℕ} (p : Point X d T) :
    IsRelativeEffectiveCartierDivisor
      (CategoryTheory.Limits.pullback.snd X.hom T.hom) p.ideal := sorry

end Point

/-- Pointwise addition of degree-`d₁` and degree-`d₂` Hilbert points. -/
def additionApp (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d₁ d₂ : ℕ) (T : (Over S)ᵒᵖ)
    (p : (functor X d₁ ⊗ functor X d₂).obj T) : Point X (d₁ + d₂) T.unop :=
  p.1.add p.2

/-- Pointwise addition of Hilbert points is natural in the test scheme. -/
theorem additionApp_naturality (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d₁ d₂ : ℕ) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (functor X d₁ ⊗ functor X d₂).map f ≫ TypeCat.ofHom (additionApp X d₁ d₂ T') =
      TypeCat.ofHom (additionApp X d₁ d₂ T) ≫ (functor X (d₁ + d₂)).map f := sorry

/-- The natural transformation `(D₁, D₂) ↦ D₁ + D₂` on Hilbert points. -/
def addition (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d₁ d₂ : ℕ) : functor X d₁ ⊗ functor X d₂ ⟶ functor X (d₁ + d₂) where
  app T := TypeCat.ofHom (additionApp X d₁ d₂ T)
  naturality := fun _ _ f ↦ additionApp_naturality X d₁ d₂ f

/-- At each test scheme, `addition` sends a pair of Hilbert points to their divisor sum. -/
theorem addition_app (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d₁ d₂ : ℕ) (T : (Over S)ᵒᵖ) (p : (functor X d₁ ⊗ functor X d₂).obj T) :
    (addition X d₁ d₂).app T p = p.1.add p.2 := sorry

/-- The morphism induced by divisor addition between explicitly chosen representing objects. -/
def additionMapWith (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d₁ d₂ : ℕ) {H₁ H₂ Hsum : Over S}
    (R₁ : (functor X d₁).RepresentableBy H₁)
    (R₂ : (functor X d₂).RepresentableBy H₂)
    (Rsum : (functor X (d₁ + d₂)).RepresentableBy Hsum) : H₁ ⊗ H₂ ⟶ Hsum :=
  (Functor.Monoidal.RepresentableBy.tensorObj R₁ R₂).map Rsum (addition X d₁ d₂)

/-- The representing equivalence sends `additionMapWith` to divisor addition applied to the
universal pair. -/
theorem additionMapWith_homEquiv (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d₁ d₂ : ℕ) {H₁ H₂ Hsum : Over S}
    (R₁ : (functor X d₁).RepresentableBy H₁)
    (R₂ : (functor X d₂).RepresentableBy H₂)
    (Rsum : (functor X (d₁ + d₂)).RepresentableBy Hsum) :
    Rsum.homEquiv (additionMapWith X d₁ d₂ R₁ R₂ Rsum) =
      (addition X d₁ d₂).app (op (H₁ ⊗ H₂))
        ((Functor.Monoidal.RepresentableBy.tensorObj R₁ R₂).homEquiv (𝟙 (H₁ ⊗ H₂))) := sorry

/-- Divisor addition between the chosen representing schemes of the Hilbert functors. -/
def additionMap (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    [∀ n : ℕ, (functor X n).IsRepresentable] (d₁ d₂ : ℕ) :
    (functor X d₁).reprX ⊗ (functor X d₂).reprX ⟶ (functor X (d₁ + d₂)).reprX :=
  additionMapWith X d₁ d₂ (functor X d₁).representableBy
    (functor X d₂).representableBy (functor X (d₁ + d₂)).representableBy

/-- The chosen addition map is the explicit-representation construction for the chosen
representations. -/
theorem additionMap_def (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    [∀ n : ℕ, (functor X n).IsRepresentable] (d₁ d₂ : ℕ) :
    additionMap X d₁ d₂ =
      additionMapWith X d₁ d₂ (functor X d₁).representableBy
        (functor X d₂).representableBy (functor X (d₁ + d₂)).representableBy := sorry

end AlgebraicGeometry.Hilbert
