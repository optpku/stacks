/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- Stacks tag `0G8Q`: the coordinate quotient is canonically isomorphic to the Rees algebra. -/
@[stacks 0G8Q "coordinate Rees presentation equivalence"]
noncomputable def equiv (n : ℕ) :
    Quotient (R := R) n ≃ₐ[
      MvPolynomial.Coordinate.base (R := R) n]
      reesAlgebra (MvPolynomial.Coordinate.center (R := R) n) :=
  AlgEquiv.ofBijective (map (R := R) n) (map_bijective (R := R) n)

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
