module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Cartesian squares of groupoid morphisms

Inversion exchanges the source and target squares of a groupoid morphism.
Their pullback property can also be read on the underlying algebraic spaces.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}

/-- The source square of a groupoid morphism is cartesian if and only if its target square is
cartesian. -/
theorem isPullback_source_iff_target (f : Hom G H) :
    IsPullback f.arrow G.s H.s f.obj ↔ IsPullback f.arrow G.t H.t f.obj := sorry

/-- The source square is cartesian over the base algebraic space if and only if the underlying
square of algebraic spaces is cartesian. -/
theorem isPullback_source_iff_left (f : Hom G H) :
    IsPullback f.arrow G.s H.s f.obj ↔
      IsPullback f.arrow.left G.s.left H.s.left f.obj.left := sorry

/-- The source square of a groupoid morphism is cartesian, obtained from the assumed target
square by inversion. -/
theorem sourceSquare_isPullback (f : Hom G H)
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    IsPullback f.arrow.left G.s.left H.s.left f.obj.left :=
  sorry

/-- Quasi-compactness of the object map of a groupoid morphism with cartesian target square
passes to the arrow map by base change. -/
theorem arrow_quasiCompact (f : Hom G H) [AlgebraicSpace.QuasiCompact f.obj.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    AlgebraicSpace.QuasiCompact f.arrow.left :=
  sorry

/-- Quasi-separatedness of the object map of a groupoid morphism with cartesian target square
passes to the arrow map by base change. -/
theorem arrow_quasiSeparated (f : Hom G H) [AlgebraicSpace.QuasiSeparated f.obj.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    AlgebraicSpace.QuasiSeparated f.arrow.left :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
