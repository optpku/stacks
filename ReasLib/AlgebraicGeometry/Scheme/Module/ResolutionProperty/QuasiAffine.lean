module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty.RelativeAmple
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Ample

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A quasi-affine morphism pulls the resolution property back from a quasi-compact and
quasi-separated target. -/
theorem hasResolutionProperty_of_quasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] (hY : HasResolutionProperty Y)
    (hf : QuasiAffineHom f) : HasResolutionProperty X := sorry

/-- An affine morphism pulls the resolution property back from a quasi-compact and
quasi-separated target. -/
theorem hasResolutionProperty_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hY : HasResolutionProperty Y) : HasResolutionProperty X := sorry

end AlgebraicGeometry.Scheme
