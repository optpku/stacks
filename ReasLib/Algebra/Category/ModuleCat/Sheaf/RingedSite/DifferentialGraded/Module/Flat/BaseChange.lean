module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-base goodness after DG-module base change

These predicates separate the algebraic content of goodness after a specified base-change functor
from the geometric choice of which base changes must be quantified.  The latter belongs to the
`RingedSite.ToposHom` layer.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe uC vC wC uD vD wD

namespace SheafOfModules.RingedSite.DifferentialGradedModule.BaseChange

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
variable [HasWeakSheafify JC AddCommGrpCat.{wC}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{wC}]
variable [HasWeakSheafify JD AddCommGrpCat.{wD}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{wD}]
variable [UnivLE.{max uC vC, wC}] [UnivLE.{max uD vD, wD}]
variable {OC : Sheaf JC CommRingCat.{wC}} {OD : Sheaf JD CommRingCat.{wD}}

variable (F : CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JC) (𝒪 := OC)) ℤ ⥤
  CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ)
variable [F.LaxMonoidal]
variable {A : DGA(OC)} {B : DGA(OD)}

/-- A right DG module is graded-flat after the specified algebraic base change. -/
@[stacks 0FSA "graded flatness after a specified base change"]
def IsGradedFlat (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B)
    (M : Mod(A, d)) : Prop :=
  DifferentialGradedModule.IsGradedFlat ((DifferentialGradedModule.baseChange F φ).obj M)

/-- Modules which are graded-flat after the specified algebraic base change. -/
abbrev gradedFlatObjects
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) : ObjectProperty Mod(A, d) :=
  fun M ↦ IsGradedFlat F φ M

/-- A right DG module is relatively K-flat after the specified algebraic base change. -/
@[stacks 0FSA "relative K-flatness after a specified base change"]
def IsKFlat (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B)
    (M : Mod(A, d)) : Prop :=
  DifferentialGradedModule.IsKFlat ((DifferentialGradedModule.baseChange F φ).obj M)

/-- Modules which are relatively K-flat after the specified algebraic base change. -/
abbrev kFlatObjects
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) : ObjectProperty Mod(A, d) :=
  fun M ↦ IsKFlat F φ M

/-- A right DG module satisfies both fixed-base goodness conditions after the specified algebraic
base change. -/
@[stacks 0FSA "goodness after a specified base change"]
def IsGoodAtBase (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B)
    (M : Mod(A, d)) : Prop :=
  DifferentialGradedModule.IsGoodAtBase ((DifferentialGradedModule.baseChange F φ).obj M)

/-- Modules satisfying both fixed-base goodness conditions after the specified base change. -/
abbrev goodAtBaseObjects
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) : ObjectProperty Mod(A, d) :=
  fun M ↦ IsGoodAtBase F φ M

/-- Goodness after a specified base change is the conjunction of its two atomic conditions. -/
theorem isGoodAtBase_iff
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) (M : Mod(A, d)) :
    IsGoodAtBase F φ M ↔ IsGradedFlat F φ M ∧ IsKFlat F φ M := sorry

end SheafOfModules.RingedSite.DifferentialGradedModule.BaseChange

end
