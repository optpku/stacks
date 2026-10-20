module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/-- The scheme-theoretic image of a section of a separated morphism over a
quasi-compact open subspace maps isomorphically to that open subspace after
restriction. -/
theorem isIso_openInverseImageTo_of_section {S : Scheme.{u}}
    {X Y V Y' : AlgebraicSpace S} (f : X ⟶ Y) [Separated f]
    (ιV : V ⟶ Y) [IsOpenImmersion ιV] [QuasiCompact ιV]
    (s : V ⟶ X) (hs : s ≫ f = ιV) (toImage : V ⟶ Y') (ι : Y' ⟶ X)
    [IsSchemeTheoreticImage s toImage ι] :
    IsIso (openInverseImageTo (ι ≫ f) ιV) := sorry

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage
