module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.LocalEquality
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Unramified

/-- If `S` and `Y.left` are Noetherian and `X.hom` is quasi-compact and unramified, then the
type of `S`-morphisms from `Y` to `X` is finite. -/
@[stacks 0AKI]
instance homFinite {S : Scheme.{u}} [IsNoetherian S] (X Y : Over S)
    [QuasiCompact X.hom] [Unramified X.hom] [IsNoetherian Y.left] :
    Finite (Y ⟶ X) := sorry

end AlgebraicGeometry.Unramified
