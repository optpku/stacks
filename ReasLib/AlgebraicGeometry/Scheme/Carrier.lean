module

public import Mathlib.AlgebraicGeometry.Scheme

universe u

@[expose] public section

namespace AlgebraicGeometry

/-- The type of schemes in universe `u`. -/
abbrev SchemeObject : Type (u + 1) := Scheme.{u}

end AlgebraicGeometry
