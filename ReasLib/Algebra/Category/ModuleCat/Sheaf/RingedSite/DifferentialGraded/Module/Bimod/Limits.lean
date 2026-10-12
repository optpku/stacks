/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Bimod.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits under the DG-module/right-module equivalence

This leaf transports shaped colimits from right differential graded modules to Mathlib right
module objects.  The forward transport is a global instance because the DG-module category is the
canonical source owner.  The reverse direction remains an explicit theorem, preventing a
typeclass loop between equivalent presentations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w uI vI

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {O : Sheaf J CommRingCat.{w}}
variable {K : Type uI} [Category.{vI} K]

/-- Shaped colimits of right DG modules canonically induce shaped colimits of the equivalent
Mathlib right module objects.  This is the only registered direction, so typeclass search cannot
cycle between the two presentations. -/
@[stacks 0FSA "right module object colimits from differential graded modules"]
noncomputable instance rightModuleHasColimitsOfShape (A : DGA(O))
    [HasColimitsOfShape K Mod(A, d)] :
    HasColimitsOfShape K (CategoryTheory.Bimod.RightModule A.toMon) := sorry

/-- Shaped colimits can be transported back from Mathlib right module objects to right DG modules.
This direction is deliberately not an instance, since registering both directions would create a
typeclass loop. -/
@[stacks 0FSA "differential graded module colimits from right module objects"]
theorem hasColimitsOfShape_of_rightModule (A : DGA(O))
    [HasColimitsOfShape K (CategoryTheory.Bimod.RightModule A.toMon)] :
    HasColimitsOfShape K Mod(A, d) := sorry

/-- The canonical comparison from the right module object associated to a DG-module colimit to
the colimit of the associated right module objects. -/
@[stacks 0FSA "right DG module colimit comparison"]
noncomputable def toBimodColimitIso {A : DGA(O)} [HasColimitsOfShape K Mod(A, d)]
    (F : K ⥤ Mod(A, d)) :
    toBimod (colimit F) ≅ colimit (F ⋙ toBimodFunctor A) :=
  preservesColimitIso (toBimodFunctor A) F

/-- The forward DG-module/right-module colimit comparison carries each mapped colimit leg to the
corresponding colimit leg. -/
@[reassoc (attr := simp)]
theorem toBimodColimitIso_hom_ι {A : DGA(O)} [HasColimitsOfShape K Mod(A, d)]
    (F : K ⥤ Mod(A, d)) (k : K) :
    (toBimodFunctor A).map (colimit.ι F k) ≫ (toBimodColimitIso F).hom =
      colimit.ι (F ⋙ toBimodFunctor A) k := sorry

/-- The inverse DG-module/right-module colimit comparison carries each colimit leg back to the
mapped DG-module colimit leg. -/
@[reassoc (attr := simp)]
theorem toBimodColimitIso_inv_ι {A : DGA(O)} [HasColimitsOfShape K Mod(A, d)]
    (F : K ⥤ Mod(A, d)) (k : K) :
    colimit.ι (F ⋙ toBimodFunctor A) k ≫ (toBimodColimitIso F).inv =
      (toBimodFunctor A).map (colimit.ι F k) := sorry

/-- The canonical comparison from the DG module extracted from a right-module-object colimit to
the colimit of the extracted DG modules. -/
@[stacks 0FSA "right module object colimit extraction comparison"]
noncomputable def ofBimodColimitIso {A : DGA(O)}
    [HasColimitsOfShape K (CategoryTheory.Bimod.RightModule A.toMon)]
    [HasColimitsOfShape K Mod(A, d)]
    (F : K ⥤ CategoryTheory.Bimod.RightModule A.toMon) :
    ofBimod (colimit F) ≅ colimit (F ⋙ ofBimodFunctor A) :=
  preservesColimitIso (ofBimodFunctor A) F

/-- The forward right-module/DG-module colimit comparison carries each mapped colimit leg to the
corresponding colimit leg. -/
@[reassoc (attr := simp)]
theorem ofBimodColimitIso_hom_ι {A : DGA(O)}
    [HasColimitsOfShape K (CategoryTheory.Bimod.RightModule A.toMon)]
    [HasColimitsOfShape K Mod(A, d)]
    (F : K ⥤ CategoryTheory.Bimod.RightModule A.toMon) (k : K) :
    (ofBimodFunctor A).map (colimit.ι F k) ≫ (ofBimodColimitIso F).hom =
      colimit.ι (F ⋙ ofBimodFunctor A) k := sorry

/-- The inverse right-module/DG-module colimit comparison carries each colimit leg back to the
mapped right-module-object colimit leg. -/
@[reassoc (attr := simp)]
theorem ofBimodColimitIso_inv_ι {A : DGA(O)}
    [HasColimitsOfShape K (CategoryTheory.Bimod.RightModule A.toMon)]
    [HasColimitsOfShape K Mod(A, d)]
    (F : K ⥤ CategoryTheory.Bimod.RightModule A.toMon) (k : K) :
    colimit.ι (F ⋙ ofBimodFunctor A) k ≫ (ofBimodColimitIso F).inv =
      (ofBimodFunctor A).map (colimit.ι F k) := sorry

variable (A : DGA(O))

#synth PreservesColimitsOfShape K (toBimodFunctor A)
#synth PreservesColimitsOfShape K (ofBimodFunctor A)

variable [HasColimitsOfShape K Mod(A, d)]

#synth HasColimitsOfShape K (CategoryTheory.Bimod.RightModule A.toMon)

end

end SheafOfModules.RingedSite.DifferentialGradedModule

end
