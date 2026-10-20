module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.AffineOpen

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeHom

/-- If `Z` is finite locally free over `S` and `X` is separated, locally of finite type,
and locally quasi-finite over `S`, then the relative-Hom functor from `Z` to `X` is
representable. -/
@[instance]
theorem isRepresentableOfSeparatedLocallyQuasiFinite {S : Scheme.{u}} (Z X : Over S)
    [IsFiniteLocallyFree Z.hom] [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [LocallyQuasiFinite X.hom] : (functor Z X).IsRepresentable := sorry

end AlgebraicGeometry.Scheme.RelativeHom
