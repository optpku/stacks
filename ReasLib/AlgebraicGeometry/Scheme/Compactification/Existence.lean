module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Existence of compactifications
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- If `X` is compactifiable over a quasi-compact quasi-separated scheme `S`, then an
`S`-morphism `f : X ⟶ Y` to a separated finite type scheme makes `X` compactifiable over `Y`. -/
@[stacks 0A9Z]
theorem nonempty_over {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    {X Y : Over S} (f : X ⟶ Y) [IsSeparated Y.hom] [Scheme.Hom.FiniteType Y.hom]
    [Nonempty (Of S X)] : Nonempty (Of Y.left (Over.mk f.left)) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of
