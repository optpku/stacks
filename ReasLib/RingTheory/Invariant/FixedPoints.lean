module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Fixed-point subrings and orbit polynomials

@stack 0BRF
@stack 0BU6

This leaf owns the bridges for restricting equivariant ring homomorphisms to
fixed-point subrings.  Its orbit-polynomial theorem is stated at the ring-map
level so quotient and tensor constructions can reuse it independently.
-/

universe u v w

open Polynomial

namespace FixedPoints

variable {G : Type u} [Group G]
variable {A : Type v} [CommRing A] [MulSemiringAction G A]

/-- the fixed-point subring is invariant over itself. -/
@[stacks 0BRF, stacks 0BRI "fixed-point subring is invariant"]
instance subring_isInvariant : Algebra.IsInvariant (FixedPoints.subring A G) A G where
  isInvariant a ha := ⟨⟨a, ha⟩, rfl⟩

/-- A finite action makes the ambient ring integral over its fixed-point subring. -/
@[stacks 0BU6 "integrality over a finite fixed-point subring"]
instance subring_isIntegral [Finite G] :
    Algebra.IsIntegral (FixedPoints.subring A G) A := sorry
-- Proof strategy: for each `a : A`, use its finite orbit polynomial
-- `MulSemiringAction.charpoly G a`; its coefficients are fixed, it is monic, and it
-- evaluates to zero at `a`.

end FixedPoints

namespace MulSemiringActionHom

variable {G : Type u} [Group G]
variable {A : Type v} {B : Type w} [CommRing A] [CommRing B]
variable [MulSemiringAction G A] [MulSemiringAction G B]

/-- restrict an equivariant ring homomorphism to fixed-point subrings. -/
@[stacks 0BRF "map on fixed-point subrings"]
def fixedPoints (φ : A →+*[G] B) :
    FixedPoints.subring A G →+* FixedPoints.subring B G :=
  RingHom.codRestrict
    ((φ : A →+* B).comp (FixedPoints.subring A G).subtype)
    (FixedPoints.subring B G) fun a g ↦ by
    simpa [MulSemiringActionHom.map_smul] using congrArg φ (a.2 g)

/-- Composing the fixed-point map with the target subtype recovers the restricted source map. -/
@[simp, stacks 0BRF "fixed-point map subtype compatibility"]
theorem subtype_comp_fixedPoints (φ : A →+*[G] B) :
    (FixedPoints.subring B G).subtype.comp φ.fixedPoints =
      (φ : A →+* B).comp (FixedPoints.subring A G).subtype :=
  rfl

variable [Finite G]

/-- a surjective equivariant map lifts the orbit polynomial of a fixed target element. -/
@[stacks 0BRF "monic orbit polynomial over fixed-point subrings"]
theorem exists_monic_map_eq_orbit (φ : A →+*[G] B) (hφ : Function.Surjective φ)
    (b : FixedPoints.subring B G) :
    ∃ P : Polynomial (FixedPoints.subring A G), P.Monic ∧
      P.map φ.fixedPoints = (X - C b) ^ Nat.card G :=
  sorry
-- Proof strategy: choose a preimage of `b`, form its monic orbit polynomial, and use
-- equivariance plus surjectivity to identify its fixed coefficients and mapped polynomial with
-- the orbit polynomial of the fixed target element.

end MulSemiringActionHom
