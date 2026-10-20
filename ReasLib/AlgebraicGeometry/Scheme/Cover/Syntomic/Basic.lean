module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic

/-!
# Syntomic covers of schemes

This module provides the canonical bundled presentation of a syntomic cover.
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- A syntomic covering of `T` represented as a canonical fixed-target
`Scheme.Cover`. -/
@[stacks 0225]
abbrev SyntomicCover (T : Scheme.{u}) :=
  T.Cover (Scheme.precoverage (@Syntomic))

end AlgebraicGeometry
