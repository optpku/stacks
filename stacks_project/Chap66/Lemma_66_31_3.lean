module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_31_3_LocallyProjective

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 66.31.3: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. Let `𝒢` be a quasi-coherent `𝒪_Y`-module. If `𝒢` is locally projective on `Y`,
then `f* 𝒢` is locally projective on `X`. -/
@[stacks 060S]
instance pullback_isLocallyProjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] [IsLocallyProjective 𝒢] :
    IsLocallyProjective ((pullback f).obj 𝒢) :=
  sorry

/-- Pullback along a morphism of algebraic spaces preserves local projectivity of quasi-coherent
modules. -/
theorem IsLocallyProjective.pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {𝒢 : Y.Modules} [𝒢.IsQuasicoherent] (h𝒢 : IsLocallyProjective 𝒢) :
    IsLocallyProjective ((pullback f).obj 𝒢) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
