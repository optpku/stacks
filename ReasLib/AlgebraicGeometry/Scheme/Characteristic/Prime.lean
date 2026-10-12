/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Prime characteristic of schemes

This leaf records that a natural number vanishes on every ring of sections of
a scheme, together with the affine-spectrum and sectionwise compatibility API.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme has characteristic `p` when `p` vanishes in the ring of sections on every open. -/
class IsCharP (X : Scheme.{u}) (p : ℕ) : Prop where
  cast_eq_zero (U : X.Opens) : (p : Γ(X, U)) = 0

/-- A scheme has characteristic `p` exactly when `p` vanishes on every ring of sections. -/
theorem isCharP_iff (X : Scheme.{u}) (p : ℕ) :
    IsCharP X p ↔ ∀ U : X.Opens, (p : Γ(X, U)) = 0 := sorry

/-- Exact characteristic `p` on every ring of sections implies scheme characteristic `p`. -/
instance instIsCharPOfSectionwiseCharP (X : Scheme.{u}) (p : ℕ)
    [∀ U : X.Opens, CharP (Γ(X, U)) p] : IsCharP X p where
  cast_eq_zero U := sorry

/-- The spectrum of a commutative ring of characteristic `p` is a scheme of characteristic `p`. -/
theorem isCharP_spec (R : Type u) [CommRing R] (p : ℕ) [CharP R p] :
    IsCharP (Spec (CommRingCat.of R)) p := sorry

/-- A commutative ring of characteristic `p` gives its spectrum the canonical scheme
characteristic `p` instance. -/
instance instIsCharPSpec (R : Type u) [CommRing R] (p : ℕ) [CharP R p] :
    IsCharP (Spec (CommRingCat.of R)) p :=
  isCharP_spec R p

end AlgebraicGeometry.Scheme
