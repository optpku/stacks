/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Quasi-compactness permanence for algebraic spaces

Morphisms from quasi-compact algebraic spaces to absolutely quasi-separated spaces
are quasi-compact. Pullbacks of quasi-compact spaces over an absolutely
quasi-separated space are quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiCompact

/-- A morphism of algebraic spaces from a quasi-compact source to a quasi-separated
target is quasi-compact. -/
instance (priority := low) of_isQuasiCompact {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y] : QuasiCompact f :=
  sorry

end QuasiCompact

namespace IsQuasiCompact

/-- The vertex of an `IsPullback` square of algebraic spaces is quasi-compact when
the two factors are quasi-compact and the target is quasi-separated. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y] [IsQuasiCompact Z]
    (h : IsPullback pZ pX g f) : IsQuasiCompact P :=
  sorry

/-- The chosen fibre product of quasi-compact algebraic spaces over a quasi-separated
target is quasi-compact. -/
instance (priority := low) instPullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y] [IsQuasiCompact Z]
    [HasPullback f g] : IsQuasiCompact (pullback f g) :=
  sorry

end IsQuasiCompact

end AlgebraicGeometry.AlgebraicSpace
