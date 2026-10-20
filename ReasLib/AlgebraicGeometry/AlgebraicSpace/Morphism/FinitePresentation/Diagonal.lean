module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Diagonals of finite presentation morphisms of algebraic spaces

The relative diagonal of a locally of finite type morphism of algebraic spaces
is locally of finite presentation. Under quasi-separatedness, the diagonal is
of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFinitePresentation

/-- The relative diagonal of a locally of finite type morphism of algebraic
spaces is locally of finite presentation. -/
instance diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (pullback.diagonal f) := sorry

end LocallyOfFinitePresentation

namespace FinitePresentation

/-- The relative diagonal of a quasi-separated locally of finite type morphism
of algebraic spaces is of finite presentation. -/
instance diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [LocallyOfFiniteType f] :
    FinitePresentation (pullback.diagonal f) := sorry

end FinitePresentation

end AlgebraicGeometry.AlgebraicSpace
