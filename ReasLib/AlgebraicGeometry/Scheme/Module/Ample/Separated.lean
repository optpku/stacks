/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A scheme covered pointwise by affine nonvanishing opens of positive tensor powers of an
invertible module is separated. -/
@[stacks 01PY]
theorem isSeparated_of_affine_nonvanishing {X : Scheme.{u}} {L : X.Modules}
    [hL : Invertible L]
    (h : ∀ x : X, ∃ n : ℕ, 0 < n ∧ ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤),
      AffineOpenNeighborhood x (hL.nonvanishingOpen s)) :
    X.IsSeparated := sorry

/-- A scheme admitting an ample invertible module is separated. -/
theorem isSeparated_of_exists_isAmple {X : Scheme.{u}}
    (h : HasAmpleInvertibleModule X) :
    X.IsSeparated := sorry

end AlgebraicGeometry.Scheme.Modules
