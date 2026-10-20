module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ideal.Torsion

/-!
# Pushforward of ideal-torsion subsheaves

For a quasi-compact and quasi-separated morphism of algebraic spaces, pushforward
identifies the subsheaf annihilated by the inverse-image finite type ideal with the
subsheaf annihilated by the original ideal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a quasi-compact and quasi-separated morphism `f : X ⟶ Y` of algebraic spaces, a
quasi-coherent finite type ideal `I ⊂ 𝒪_Y`, and a quasi-coherent `𝒪_X`-module `ℱ`, the image of
`f_*` of the torsion inclusion of `ℱ` along `I.pullback f` equals, on every object of the small
étale site of `Y`, the image of the torsion inclusion of `f_* ℱ` along `I`. Here `I.pullback f` is
the inverse-image ideal `f⁻¹I 𝒪_X`. -/
theorem range_pushforward_idealTorsionSubsheafι_app_eq
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (I : IdealSubobject Y) [(I : Y.Modules).IsQuasicoherent] [(I : Y.Modules).IsFiniteType]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : smallEtaleSite Y) :
    Set.range (((pushforward f).map (idealTorsionSubsheafι (I.pullback f) ℱ)).val.app (op U)) =
      Set.range ((idealTorsionSubsheafι I ((pushforward f).obj ℱ)).val.app (op U)) :=
  sorry

/-- The pushed-forward inclusion of the subsheaf annihilated by `f⁻¹I 𝒪_X` and the inclusion of
the subsheaf of `f_* ℱ` annihilated by `I` determine the same subobject of `f_* ℱ`. -/
theorem imageSubobject_pushforward_idealTorsionSubsheafι_eq
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (I : IdealSubobject Y) [(I : Y.Modules).IsQuasicoherent] [(I : Y.Modules).IsFiniteType]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    imageSubobject ((pushforward f).map (idealTorsionSubsheafι (I.pullback f) ℱ)) =
      imageSubobject (idealTorsionSubsheafι I ((pushforward f).obj ℱ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
