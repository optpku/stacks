module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

/-! # Composition of conormal morphisms -/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry (Scheme)

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal

variable {S : Scheme.{u}}

/-- For a vertically stacked pair of commutative squares of algebraic spaces whose
horizontal arrows are immersions, `Hom.Conormal.map` of the composite square is the
composite of `Hom.Conormal.map` of the lower square with the pullback of
`Hom.Conormal.map` of the upper square. -/
theorem map_comp {Z X Z' X' Z'' X'' : AlgebraicSpace S} {f : Z ⟶ Z'} {f' : Z' ⟶ Z''}
    {i : Z ⟶ X} {i' : Z' ⟶ X'} {i'' : Z'' ⟶ X''} {g : X ⟶ X'} {g' : X' ⟶ X''}
    [IsImmersion i] [IsImmersion i'] [IsImmersion i''] (sq : CommSq f i i' g)
    (sq' : CommSq f' i' i'' g') :
    Hom.Conormal.map (sq.horiz_comp sq') =
      (Modules.pullbackCompIso f f').inv.app (Hom.conormalSheaf i'') ≫
        (Modules.pullback f).map (Hom.Conormal.map sq') ≫ Hom.Conormal.map sq :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal
