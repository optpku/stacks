module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Filtration.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification

/-!
# Invertible-quotient filtrations after modification

This module relates finite locally free scheme modules to filtrations with
invertible successive quotients on a modification.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free module on an integral scheme acquires an invertible-quotient
filtration after pullback along a modification. -/
@[stacks 0AYP "finite locally free modules acquire invertible-quotient filtrations after modification"]
theorem exists_modification_with_invertibleQuotientFiltration
    (X : Scheme.{u}) [IsIntegral X] (E : X.Modules) [IsFiniteLocallyFree E] :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X),
      IsModification f ∧ HasInvertibleQuotientFiltration ((pullback f).obj E) := sorry

end AlgebraicGeometry.Scheme.Modules
