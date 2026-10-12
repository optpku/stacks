/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.QuasiCompact

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Lemma 110.80.2: the scheme `Spec ℤ` is not a quasi-compact object of
`Sheaf.canonicalTopology Scheme`. This is the site-object property
`GrothendieckTopology.QuasiCompactObject`, not topological quasi-compactness of
the underlying space of `Spec ℤ`. -/
@[stacks 0EUG]
theorem specInt_not_quasiCompactObject :
    ¬ (Sheaf.canonicalTopology Scheme.{u}).QuasiCompactObject
      (Spec (.of (ULift.{u} ℤ))) := sorry

end AlgebraicGeometry
