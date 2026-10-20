module

public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Lift.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatibility names for lifts to selected cochain representatives

The neutral owner is `DerivedCategory.Preimage.Lift`.  This file keeps the historical
truncation-spectral-sequence name as a reducible compatibility abbreviation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB uC vC

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]

namespace Realization

/-- Compatibility abbreviation for a lift between the selected representatives of derived
objects.  New code should use `DerivedCategory.Preimage.Lift`. -/
@[stacks 0BKM "cochain lift of a derived morphism for truncation filtration"]
abbrev Lift {K L : DerivedCategory A} (f : K ⟶ L) :=
  DerivedCategory.Preimage.Lift f

namespace Lift

export _root_.CategoryTheory.DerivedCategory.Preimage.Lift (map_eq)

end Lift

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
