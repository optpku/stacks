/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.ReesAlgebra.Presentation
public import ReasLib.RingTheory.MvPolynomial.Coordinate

/-!
# Coordinate Rees presentation

This leaf specializes the generic pair-relation presentation to the ideal of
variables in a polynomial ring.  The coordinate case is the linear-type case:
the quotient map is an isomorphism, while the generic presentation layer makes
no such claim.
-/

@[expose] public section

noncomputable section

universe u

open MvPolynomial

namespace ReesAlgebra.Presentation.Coordinate

variable {R : Type u} [CommRing R]

/-! ## Coordinate data and presentation -/

/-- Stacks tag `0G8Q`: the outer polynomial ring for the coordinate Rees presentation. -/
@[stacks 0G8Q "coordinate Rees presentation polynomial ring"]
abbrev ambient (n : ℕ) :=
  MvPolynomial (Fin n) (MvPolynomial.Coordinate.base (R := R) n)

/-- Stacks tag `0G8Q`: the coordinate family of generators of the variable ideal. -/
@[stacks 0G8Q "coordinate Rees presentation generators"]
abbrev generator (n : ℕ) : Fin n → MvPolynomial.Coordinate.center (R := R) n :=
  MvPolynomial.Coordinate.generator (R := R) n

/-- Stacks tag `0G8Q`: the coordinate pair relation. -/
@[stacks 0G8Q "coordinate Rees presentation relation"]
abbrev relation (n : ℕ) (i j : Fin n) :=
  ReesAlgebra.Presentation.relation (generator (R := R) n) i j

/-- Stacks tag `0G8Q`: the coordinate relation ideal. -/
@[stacks 0G8Q "coordinate Rees presentation relation ideal"]
abbrev relationIdeal (n : ℕ) :=
  ReesAlgebra.Presentation.relationIdeal (generator (R := R) n)

/-- Stacks tag `0G8Q`: the quotient by the coordinate pair relations. -/
@[stacks 0G8Q "coordinate Rees presentation quotient"]
abbrev Quotient (n : ℕ) :=
  ReesAlgebra.Presentation.Quotient (generator (R := R) n)

/-- Stacks tag `0G8Q`: the canonical coordinate quotient-to-Rees map. -/
@[stacks 0G8Q "coordinate Rees presentation map"]
noncomputable abbrev map (n : ℕ) :
    Quotient (R := R) n →ₐ[
      MvPolynomial.Coordinate.base (R := R) n]
      reesAlgebra (MvPolynomial.Coordinate.center (R := R) n) :=
  ReesAlgebra.Presentation.map (generator (R := R) n)

/-- Stacks tag `0G8Q`: the coordinate quotient map is surjective. -/
@[stacks 0G8Q "coordinate Rees presentation surjective"]
theorem map_surjective (n : ℕ) : Function.Surjective (map (R := R) n) := sorry

/-- Stacks tag `0G8Q`: the coordinate evaluation kernel is exactly the pair-relation ideal. -/
@[stacks 0G8Q "coordinate Rees presentation kernel"]
theorem toRees_ker_eq_relationIdeal (n : ℕ) :
    RingHom.ker (ReesAlgebra.Presentation.toRees (generator (R := R) n)).toRingHom =
      relationIdeal (R := R) n := sorry

/-- Stacks tag `0G8Q`: the coordinate quotient map is injective. -/
@[stacks 0G8Q "coordinate Rees presentation injective"]
theorem map_injective (n : ℕ) : Function.Injective (map (R := R) n) := sorry

/-- Stacks tag `0G8Q`: the coordinate quotient map is bijective. -/
@[stacks 0G8Q "coordinate Rees presentation bijective"]
theorem map_bijective (n : ℕ) : Function.Bijective (map (R := R) n) := sorry

/-! ## Explicit inverse by monomial straightening -/

/-- Select up to `e` factors from a monomial, in increasing coordinate order. -/
@[expose] def splitExponent {n : ℕ} (e : ℕ) (d : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.onFinset Finset.univ
    (fun i ↦ min (d i) (e - ∑ j ∈ Finset.univ.filter (fun j ↦ j < i), d j))
    (by simp)

/-- The selected factors occur in the original monomial. -/
private theorem splitExponent_le {n : ℕ} (e : ℕ) (d : Fin n →₀ ℕ) :
    splitExponent e d ≤ d := sorry

/-- Greedy selection takes the requested number of factors, up to the available degree. -/
private theorem splitExponent_sum {n : ℕ} (e : ℕ) (d : Fin n →₀ ℕ) :
    (splitExponent e d).sum (fun _ k ↦ k) = min e (d.sum (fun _ k ↦ k)) := sorry

/-- Lift a coefficient of Rees degree `e` by splitting each coordinate monomial into
base and presentation variables. -/
@[expose] def coefficientLift (n e : ℕ) (p : MvPolynomial.Coordinate.base (R := R) n) :
    ambient (R := R) n :=
  ∑ d ∈ p.support,
    monomial (splitExponent e d) (monomial (d - splitExponent e d) (coeff d p))

/-- Straighten each monomial of a coordinate Rees element into its presentation quotient. -/
noncomputable def inverse (n : ℕ) :
    reesAlgebra (MvPolynomial.Coordinate.center (R := R) n) →ₐ[
      MvPolynomial.Coordinate.base (R := R) n] Quotient (R := R) n where
  toFun p := Ideal.Quotient.mk (relationIdeal (R := R) n)
    (p.1.sum (fun e c ↦ coefficientLift n e c))
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry
  commutes' := by sorry

/-- Straightening reverses coordinate Rees evaluation. -/
theorem inverse_map (n : ℕ) (p : Quotient (R := R) n) :
    inverse n (map n p) = p := sorry

/-- Evaluating a straightened Rees element recovers that element. -/
theorem map_inverse (n : ℕ)
    (p : reesAlgebra (MvPolynomial.Coordinate.center (R := R) n)) :
    map n (inverse n p) = p := sorry

/-- The inverse sends a degree-one coordinate generator to its presentation variable. -/
@[simp]
theorem inverse_degreeOne (n : ℕ) (i : Fin n) :
    inverse (R := R) n
        (ReesAlgebra.Grading.degreeOne
          (MvPolynomial.Coordinate.center (R := R) n) (generator (R := R) n i)) =
      Ideal.Quotient.mk (relationIdeal (R := R) n) (X i : ambient (R := R) n) := sorry

/-- Stacks tag `0G8Q`: the coordinate quotient is canonically isomorphic to the Rees algebra. -/
@[stacks 0G8Q "coordinate Rees presentation equivalence"]
noncomputable def equiv (n : ℕ) :
    Quotient (R := R) n ≃ₐ[
      MvPolynomial.Coordinate.base (R := R) n]
      reesAlgebra (MvPolynomial.Coordinate.center (R := R) n) :=
  { map (R := R) n with
    invFun := inverse n
    left_inv := inverse_map n
    right_inv := map_inverse n }

/-- The reverse equivalence is the explicit monomial-straightening homomorphism. -/
@[simp]
theorem equiv_symm_apply (n : ℕ)
    (p : reesAlgebra (MvPolynomial.Coordinate.center (R := R) n)) :
    (equiv n).symm p = inverse n p := rfl

/-- The reverse equivalence sends a degree-one coordinate generator to its variable class. -/
@[simp]
theorem equiv_symm_apply_degreeOne (n : ℕ) (i : Fin n) :
    (equiv (R := R) n).symm
        (ReesAlgebra.Grading.degreeOne
          (MvPolynomial.Coordinate.center (R := R) n) (generator (R := R) n i)) =
      Ideal.Quotient.mk (relationIdeal (R := R) n) (X i : ambient (R := R) n) :=
  inverse_degreeOne n i

/-- Stacks tag `0G8Q`: the coordinate equivalence sends a quotient variable to its degree-one
Rees generator. -/
@[stacks 0G8Q "coordinate Rees presentation variable evaluation", simp]
theorem equiv_apply_variable (n : ℕ) (i : Fin n) :
    equiv (R := R) n
        (Ideal.Quotient.mk (relationIdeal (R := R) n)
          (X i : ambient (R := R) n)) =
      ReesAlgebra.Grading.degreeOne
        (MvPolynomial.Coordinate.center (R := R) n)
        (generator (R := R) n i) := sorry

end ReesAlgebra.Presentation.Coordinate
