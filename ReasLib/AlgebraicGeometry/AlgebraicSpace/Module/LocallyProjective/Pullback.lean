module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Pullback of locally projective modules on algebraic spaces

Pullback along a morphism of algebraic spaces preserves local projectivity of
quasi-coherent module sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Pullback along a morphism of algebraic spaces preserves local projectivity of quasi-coherent
modules. -/
theorem IsLocallyProjective.pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {𝒢 : Y.Modules} [𝒢.IsQuasicoherent] (h𝒢 : IsLocallyProjective 𝒢) :
    IsLocallyProjective ((pullback f).obj 𝒢) :=
  sorry

/-- The pullback of a locally projective quasi-coherent module along any morphism of algebraic
spaces is locally projective. -/
instance pullback_isLocallyProjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] [IsLocallyProjective 𝒢] :
    IsLocallyProjective ((pullback f).obj 𝒢) :=
  IsLocallyProjective.pullback f (inferInstance : IsLocallyProjective 𝒢)

end AlgebraicGeometry.AlgebraicSpace.Modules
