/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme

universe u

@[expose] public section

namespace AlgebraicGeometry

/-- The type of schemes in universe `u`. -/
abbrev SchemeObject : Type (u + 1) := Scheme.{u}

end AlgebraicGeometry
