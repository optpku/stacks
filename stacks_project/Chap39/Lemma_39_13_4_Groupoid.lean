module

public import stacks_project.Chap39.Definition_39_13_1_GroupoidScheme

/-!
# Compatibility name for groupoid schemes

This module preserves the earlier `Scheme.Groupoid` spelling while the canonical owner is
`AlgebraicGeometry.GroupoidScheme`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Compatibility spelling for the canonical `AlgebraicGeometry.GroupoidScheme` owner. -/
abbrev Groupoid (S : Scheme.{u}) := AlgebraicGeometry.GroupoidScheme S

end AlgebraicGeometry.Scheme
