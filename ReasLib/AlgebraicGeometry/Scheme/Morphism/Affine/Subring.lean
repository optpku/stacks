/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

/-!
# Affine spectrum morphisms from subrings

This module records element-existence consequences for a proper subring whose induced morphism of
affine spectra is a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.UniversalHomeomorphism

variable {B : Type u} [CommRing B]

/-- A proper subring whose induced morphism of spectra is a universal homeomorphism and induces
isomorphisms on residue fields omits an element whose square and cube belong to the subring. -/
theorem exists_not_mem_sq_cube_mem_of_residueFieldMap_isIso
    (A : Subring B)
    (hSpec : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom A.subtype)))
    (hκ :
      ∀ x : Spec (CommRingCat.of B),
        IsIso ((Spec.map (CommRingCat.ofHom A.subtype)).residueFieldMap x))
    (hneq : A ≠ ⊤) :
    ∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A := sorry

/-- For a proper subring whose induced morphism of spectra is a universal homeomorphism, either an
element outside the subring has its square and cube in the subring, or an element outside the
subring has both its multiple by some prime and its corresponding prime power in the subring. -/
theorem exists_not_mem_sq_cube_or_prime_mul_power_mem
    (A : Subring B)
    (hSpec : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom A.subtype)))
    (hneq : A ≠ ⊤) :
    (∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A) ∨
      ∃ (p : ℕ) (b : B), Nat.Prime p ∧ b ∉ A ∧ (p : B) * b ∈ A ∧ b ^ p ∈ A := sorry

end AlgebraicGeometry.UniversalHomeomorphism
