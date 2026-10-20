module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree.Finite
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite Cell Retracts in Derived Categories

This leaf packages the derived-category property of being a retract of the
image of a cochain complex with a finite cell filtration.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

/-- A derived object is a finite cell retract when it is a retract of the image of a cochain
complex that admits a finite cell filtration. -/
@[stacks 09R3 "finite cell retracts"]
def IsFiniteCellRetract (E : DerivedCategory (ModuleCat A)) : Prop :=
  ∃ P : ModuleCat.DGMod A, SemiFreeFiltration.HasFiniteCellFiltration P ∧
    Nonempty (Retract E (DerivedCategory.Q.obj P))

/-- The explicit retract formulation of `IsFiniteCellRetract`. -/
theorem isFiniteCellRetract_iff (E : DerivedCategory (ModuleCat A)) :
    IsFiniteCellRetract E ↔
      ∃ P : ModuleCat.DGMod A, SemiFreeFiltration.HasFiniteCellFiltration P ∧
        Nonempty (Retract E (DerivedCategory.Q.obj P)) := sorry

/-- A finite cell retract is compact in the derived category of modules. -/
theorem isCompactObject_of_isFiniteCellRetract
    {E : DerivedCategory (ModuleCat A)} (hE : IsFiniteCellRetract E) :
    IsCompactObject E := sorry

/-- Every compact object in the derived category of modules is a finite cell retract. -/
theorem isFiniteCellRetract_of_isCompactObject
    {E : DerivedCategory (ModuleCat A)} (hE : IsCompactObject E) :
    IsFiniteCellRetract E := sorry

/-- Compact derived objects are precisely finite cell retracts. -/
@[stacks 09R3]
theorem isCompactObject_iff_isFiniteCellRetract (E : DerivedCategory (ModuleCat A)) :
    IsCompactObject E ↔ IsFiniteCellRetract E := sorry

end CochainComplex
