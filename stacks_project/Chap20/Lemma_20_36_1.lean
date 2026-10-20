module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Power
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.Sequential
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.Quotient.Kernel
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SequentialInverseSystem
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Lemma 20.36.1 (0H39) is organized around four conditions on a one-based tower.
The reusable owners are the four presentation predicates in
`SequentialInverseSystem.PrincipalTorsion`; the declarations below retain only the source-facing
condition names and labeled equivalence bridges. -/

/-- Lemma 20.36.1 (0H39): source-facing divisibility predicate for a global-section action. -/
abbrev IsDivisibleByGlobalSection
    (f : globalSectionsRing X) (M : X.Modules) : Prop :=
  GlobalSections.Power.IsDivisible f M

/-- Lemma 20.36.1 (0H39): source-facing torsion-freeness predicate for a global-section action. -/
abbrev IsTorsionFreeByGlobalSection
    (f : globalSectionsRing X) (M : X.Modules) : Prop :=
  GlobalSections.Power.IsTorsionFree f M

/-- Lemma 20.36.1 (0H39), condition `(1)`, exposed through the reusable principal-torsion owner. -/
abbrev stepShortExactCondition
    (f : globalSectionsRing X) (F : SequentialInverseSystem X.Modules) : Prop :=
  PrincipalTorsion.IsPresented f F

/-- Lemma 20.36.1 (0H39), condition `(2)`, exposed through the reusable principal-torsion owner. -/
abbrev powerShortExactCondition
    (f : globalSectionsRing X) (F : SequentialInverseSystem X.Modules) : Prop :=
  PrincipalTorsion.IsPowerPresented f F

/-- Lemma 20.36.1 (0H39), condition `(3)`, exposed through the reusable principal-torsion owner. -/
abbrev divisibleKernelTowerCondition
    (f : globalSectionsRing X) (F : SequentialInverseSystem X.Modules) : Prop :=
  PrincipalTorsion.IsKernelPresented f F

/-- Lemma 20.36.1 (0H39), condition `(4)`, exposed through the reusable principal-torsion owner. -/
abbrev torsionFreeQuotientTowerCondition
    (f : globalSectionsRing X) (F : SequentialInverseSystem X.Modules) : Prop :=
  PrincipalTorsion.IsQuotientPresented f F

/- Lemma 20.36.1 (0H39), source-facing scalar glue is owned by `GlobalSections.Power`. -/
@[stacks 0H39 "power multiplication composition"]
#check @GlobalSections.Power.globalSectionMul_comp_smulPow

@[stacks 0H39 "unit global-section multiplication"]
#check @GlobalSections.Power.globalSectionMul_one

@[stacks 0H39 "naturality of power multiplication"]
#check @GlobalSections.Power.smulPow_natural

/-- Lemma 20.36.1 (0H39), `(3) ↔ (2)`: the divisible-kernel and power-row conditions are equivalent. -/
@[stacks 0H39 "kernel condition and power condition"]
theorem divisibleKernelTowerCondition_iff_powerShortExactCondition
    (f : globalSectionsRing X) (F : SequentialInverseSystem X.Modules) :
    divisibleKernelTowerCondition f F ↔ powerShortExactCondition f F := sorry

/-- Lemma 20.36.1 (0H39), `(2) ↔ (1)`: the power-row and stepwise conditions are equivalent. -/
@[stacks 0H39 "power condition and step condition"]
theorem powerShortExactCondition_iff_stepShortExactCondition
    (f : globalSectionsRing X) (F : SequentialInverseSystem X.Modules) :
    powerShortExactCondition f F ↔ stepShortExactCondition f F := sorry

/-- Lemma 20.36.1 (0H39), `(4) → (3)`: a torsion-free quotient presentation gives a divisible
kernel presentation.  The exact sequential-colimit instances are supplied by the reusable
Grothendieck support owner for `X.Modules`. -/
@[stacks 0H39 "quotient condition implies kernel condition"]
theorem torsionFreeQuotientTowerCondition_imp_divisibleKernelTowerCondition
    (f : globalSectionsRing X) (F : SequentialInverseSystem X.Modules) :
    torsionFreeQuotientTowerCondition f F → divisibleKernelTowerCondition f F := sorry

#check @globalSectionMul
#check @GlobalSections.Power.IsDivisible
#check @GlobalSections.Power.IsTorsionFree
#check @GlobalSections.Power.smulPow_eq_globalSectionMul
#check @GlobalSections.Power.isDivisible_iff_linear
#check @GlobalSections.Power.isTorsionFree_iff_linear
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Presentation
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.PowerPresentation
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.KernelPresentation
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsPresented
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsPowerPresented
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsKernelPresented
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsQuotientPresented
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.isPresented_iff_one_le
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.isPowerPresented_iff_one_le

@[stacks 0H39 "condition (1)"]
#check @stepShortExactCondition

@[stacks 0H39 "condition (2)"]
#check @powerShortExactCondition

@[stacks 0H39 "condition (3)"]
#check @divisibleKernelTowerCondition

@[stacks 0H39 "condition (4)"]
#check @torsionFreeQuotientTowerCondition

@[stacks 0H39 "condition (4) implies condition (3)"]
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.isKernelPresented_of_isQuotientPresented

end AlgebraicGeometry.RingedSpace
