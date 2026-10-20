module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Strict morphisms of thickenings as cartesian squares

A morphism of thickenings of ringed spaces is strict precisely when its
commutative square is cartesian.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

/-- The canonical comparison map on kernel ideals of a morphism of ringed-space
thickenings is epimorphic if and only if its defining square is a pullback. -/
theorem isStrict_iff_isPullback {T U : Thickening.{u}} (g : T ⟶ U) :
    Epi (idealMap g) ↔ IsPullback T.hom g.left g.right U.hom := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom
