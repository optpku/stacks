module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Compact.FiniteCell
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (E : DifferentialGradedModule.Derived.Category.{u, v} A)

/-!
# Proposition 22.36.4 (09R3)

An object of the intrinsic derived category of a DGA is compact exactly when it belongs to the
canonical retract closure of the finite-cell objects.
-/

@[stacks 09R3] #check
  (DifferentialGradedModule.Derived.FiniteCell.isCompactObject_iff_mem_retractClosure A E :
    IsCompactObject E ↔
      (DifferentialGradedModule.Derived.finiteCell A).retractClosure E)
#check @DifferentialGradedModule.Derived.finiteCell
#check @DifferentialGradedModule.Derived.finiteCell_iff
#check @CategoryTheory.ObjectProperty.retractClosure
