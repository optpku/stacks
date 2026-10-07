module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- If `Y` is quasi-compact and quasi-separated and has the resolution property, then a
morphism `f : X ⟶ Y` admitting a relatively ample module on `X` transfers the resolution
property to `X`. -/
theorem hasResolutionProperty_of_exists_relativelyAmple {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] (hY : HasResolutionProperty Y)
    (hL : ∃ L : X.Modules, RelativelyAmple f L) : HasResolutionProperty X := sorry

end AlgebraicGeometry.Scheme
