module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.SectionAction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular local-section actions on module sheaves

This file characterizes monicity of a local-section action by regularity of its germs on the
canonical stalk modules.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Multiplication by a local section is monic exactly when each of its germs acts regularly on
the corresponding stalk module. -/
@[stacks 0GT5 "local-section regularity"]
theorem sectionAction_mono_iff
    (M : X.Modules) (U : Opens X) (s : X.presheaf.obj (op U)) :
    Mono (SheafOfModules.sectionAction X.sheaf M U s) ↔
      ∀ (x : X) (hx : x ∈ U),
        IsSMulRegular (stalkModuleCat M x) (X.presheaf.germ U x hx s) := sorry

end AlgebraicGeometry.RingedSpace
