/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Characteristic of scheme sections

This leaf records the sectionwise characteristic inherited by affine schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- If a commutative ring has characteristic `p`, then every section on an open of its spectrum
has characteristic `p`. -/
theorem charP_opens_spec (R : Type u) [CommRing R] (p : ℕ) [CharP R p] :
    ∀ U : (Spec (CommRingCat.of R)).Opens, CharP (Γ(Spec (CommRingCat.of R), U)) p := sorry

end AlgebraicGeometry.Scheme
