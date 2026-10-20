/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Bimod.Equivalence
public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of differential graded module sheaves

Base change is transported through the canonical equivalence between differential graded modules
and right module objects.  Its data is the composite of monoidal transport and balanced extension
of scalars; homogeneous action maps are not reconstructed separately.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe uC vC wC uD vD wD

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

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

/-- Base change of right differential graded modules: pass to right module objects, transport them
along the lax monoidal functor, extend scalars along the displayed algebra morphism, and return to
the homogeneous differential graded module presentation. -/
@[stacks 0FSA "differential graded module base change"]
noncomputable def baseChange {A : DGA(OC)} {B : DGA(OD)}
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) :
    Mod(A, d) ⥤ Mod(B, d) :=
  toBimodFunctor A ⋙
    F.baseChangeRight A.toMon (DifferentialGradedAlgebra.mapHomToMon F φ) ⋙
    ofBimodFunctor B

/-- Evaluating differential graded module base change is the corresponding right-module-object
base change followed by extraction of homogeneous action maps. -/
@[simp]
theorem baseChange_obj {A : DGA(OC)} {B : DGA(OD)}
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) (M : Mod(A, d)) :
    (baseChange F φ).obj M =
      ofBimod ((F.baseChangeRight A.toMon
        (DifferentialGradedAlgebra.mapHomToMon F φ)).obj
          (toBimod (𝒪 := OC) M)) := sorry

/-- The underlying cochain complex of a base-changed differential graded module is the carrier of
the corresponding base-changed right module object. -/
@[simp]
theorem baseChange_obj_toComplex {A : DGA(OC)} {B : DGA(OD)}
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) (M : Mod(A, d)) :
    ((baseChange F φ).obj M).toComplex =
      ((F.baseChangeRight A.toMon
        (DifferentialGradedAlgebra.mapHomToMon F φ)).obj
          (toBimod (𝒪 := OC) M)).X := sorry

-- The functor data is the explicit composite displayed in `baseChange`; `sorryAx` may occur only
-- through proof-law fields of the monoidal, bimodule, and homogeneous-module bridges.

end

end SheafOfModules.RingedSite.DifferentialGradedModule

end
