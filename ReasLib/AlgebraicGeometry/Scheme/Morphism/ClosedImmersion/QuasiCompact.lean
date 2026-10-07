module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Quasi-compactness of closed immersions

Closed immersions of schemes are quasi-compact.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A closed immersion of schemes is quasi-compact. -/
theorem IsClosedImmersion.quasiCompact
    {X Y : Scheme.{u}} {f : X ⟶ Y} (h : IsClosedImmersion f) :
    QuasiCompact f := sorry

/-- Closed immersions are canonically quasi-compact. -/
instance instQuasiCompactOfIsClosedImmersion
    {X Y : Scheme.{u}} {f : X ⟶ Y} [h : IsClosedImmersion f] :
    QuasiCompact f :=
  h.quasiCompact

end AlgebraicGeometry
