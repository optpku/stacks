/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.Functor
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The fpqc sheaf property of the Hilbert functor
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Hilbert

/-- The functor of degree-`d` finite locally free closed subschemes of `X` is a sheaf for
the fpqc topology on schemes over the base. -/
theorem functor_isSheaf_fpqc {S : Scheme.{u}} (X : Over S) (d : ℕ) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (functor X d) := sorry

end AlgebraicGeometry.Hilbert
