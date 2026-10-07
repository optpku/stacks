module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap67.Lemma_67_8_10_Instances
public import stacks_project.Chap66.Definition_66_3_1_Separation

/-!
# Fibre products of quasi-compact quasi-separated algebraic spaces

The vertex of a pullback of algebraic spaces inherits quasi-compactness from the
two factors when the target is quasi-separated, and inherits absolute
quasi-separatedness from the two factors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

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

namespace IsAbsolutelyQuasiSeparated

/-- The vertex of an `IsPullback` square of algebraic spaces is quasi-separated when
the two factors are quasi-separated. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
    [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyQuasiSeparated Z]
    (h : IsPullback pZ pX g f) : IsAbsolutelyQuasiSeparated P :=
  sorry

/-- The chosen fibre product of quasi-separated algebraic spaces is quasi-separated. -/
instance (priority := low) instPullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyQuasiSeparated Z]
    [HasPullback f g] : IsAbsolutelyQuasiSeparated (pullback f g) :=
  sorry

end IsAbsolutelyQuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
