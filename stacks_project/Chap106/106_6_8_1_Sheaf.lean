module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Automorphism

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

/- 106.6.8.1: The canonical diagonal-action sheaf isomorphism. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.parameterAutIso :
  ∀ {S : Scheme.{u}} {U U' I I' : AlgebraicSpace S}
    (iU : U ⟶ U') (iI : I ⟶ I') (p' : I' ⟶ U') (p : I ⟶ U)
    (Δ' : U' ⟶ I') (Δ : U ⟶ I)
    [IsFirstOrderThickening iU] [IsFirstOrderThickening iI]
    (hΔ : IsPullback Δ iU iI Δ') (hp : IsPullback p iI iU p')
    (hsec : Δ' ≫ p' = 𝟙 U'),
    Hom.Deformation.parameterSheafEtale iU p Δ ≅
      Hom.Deformation.autSheaf iU iI p' Δ' Δ hΔ)
