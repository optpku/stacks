module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsFinite

/-- A morphism of schemes is finite if and only if it satisfies any of the equivalent
conditions involving properness, local quasi-finiteness, or universal closedness and
finite point-set fibres. -/
theorem proper_finiteFibers_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE
      [ IsFinite f
      , IsProper f ∧ ∀ s : S, Set.Finite (f ⁻¹' ({s} : Set S))
      , IsProper f ∧ LocallyQuasiFinite f
      , UniversallyClosed f ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧
          ∀ s : S, Set.Finite (f ⁻¹' ({s} : Set S)) ] := sorry

end AlgebraicGeometry.IsFinite
