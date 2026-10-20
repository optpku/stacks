module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.CountableGeneration
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Countable Generation of Differential Graded Derived Categories

This leaf specializes the compact-generator countability criterion to the canonical derived
category of a cochain differential graded algebra.  It owns the countable-cohomology predicates
and the bridges identifying them with shifted Hom types represented by the regular module.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory

universe u v

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- A cochain differential graded algebra has countable cohomology when every cohomology
module has a countable underlying type. -/
@[stacks 0CRM "countable cohomology of a differential graded algebra"]
def HasCountableCohomology (A : CochainDGAlgebra.{u, v} R) : Prop :=
  ∀ n : ℤ, Countable (A.homology n)

end CochainDGAlgebra

namespace DifferentialGradedModule.Derived

variable {R : Type u} [CommRing R]

/-- The intrinsic object property of having countable cohomology in every degree. -/
@[stacks 0CRM "countable homology object property"]
def countableHomology (A : CochainDGAlgebra.{u, v} R) :
    ObjectProperty (Category.{u, v} A) :=
  fun X ↦ ∀ n : ℤ, Countable ((homologyFunctor A n).obj X)

/-- For an actual differential graded module, derived countable homology is exactly
countability of its ordinary homology modules. -/
@[stacks 0CRM "countable homology of a represented DG module"]
theorem countableHomology_qObj_iff (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) :
    countableHomology A ((Q A).obj ((toK A).obj M)) ↔
      ∀ n : ℤ, Countable (M.homology n) := sorry

/-- The regular derived object has countable homology exactly when the differential graded
algebra has countable cohomology. -/
@[stacks 0CRM "countable homology of the regular derived object"]
theorem countableHomology_regularObject_iff (A : CochainDGAlgebra.{u, v} R) :
    countableHomology A (regularObject A) ↔ A.HasCountableCohomology := sorry

/-- Shifted Hom types represented by the regular object are countable exactly when the target
has countable cohomology. -/
@[stacks 0CRM "countable shifted Hom from the regular object"]
theorem countableShiftedHomFrom_regularObject_iff
    (A : CochainDGAlgebra.{u, v} R) (X : Category.{u, v} A) :
    countableShiftedHomFrom (regularObject A) X ↔ countableHomology A X := sorry

/-- Lemma 22.38.3 (0CRM): if a cochain differential graded algebra has countable cohomology,
then a derived module is a sequential homotopy colimit of compact objects exactly when all of
its cohomology modules are countable. -/
@[stacks 0CRM "countable homology in a differential graded derived category"]
theorem sequentialHomotopyColimits_iff_countableHomology
    (A : CochainDGAlgebra.{u, v} R) (hA : A.HasCountableCohomology)
    (X : Category.{u, v} A) :
    sequentialHomotopyColimits
        (IsCompactObject : ObjectProperty (Category.{u, v} A)) X ↔
      countableHomology A X := sorry

end DifferentialGradedModule.Derived
