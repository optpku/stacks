module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite morphisms of schemes
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A morphism of schemes is finite when it satisfies the canonical finite-morphism property. -/
abbrev IsFinite {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  _root_.AlgebraicGeometry.IsFinite f

end AlgebraicGeometry.Scheme
