module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.QuasiCompact

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The spectrum of the integers is not a quasi-compact object for the canonical
Grothendieck topology on schemes, despite being topologically quasi-compact. -/
@[stacks 0EUG]
theorem specInt_not_quasiCompactObject :
    ¬ (Sheaf.canonicalTopology Scheme.{u}).QuasiCompactObject
      (Spec (.of (ULift.{u} ℤ))) := sorry

end AlgebraicGeometry
