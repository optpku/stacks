/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Contravariant set-valued functors on schemes. -/
abbrev Presheaf : Type (u + 1) :=
  CategoryTheory.Functor AlgebraicGeometry.Scheme.{u}ᵒᵖ (Type u)

end AlgebraicGeometry.Scheme
