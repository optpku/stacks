module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
import StacksCheckRecall

/-!
# Equation 18.19.2.1

Compatibility facade for the reusable represented-sections equivalence owned by
`SheafOfModules.Localization.structureModuleHomEquiv`.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace SheafOfModules.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{w}) (U : C)
variable [(restriction R U : SheafOfModules.{w} R ⥤
  SheafOfModules.{w} (R.over U)).IsRightAdjoint]
variable (M : SheafOfModules.{w} R)

/- Equation 18.19.2.1 (0G1V): morphisms from `j_{U!} R_U` to `M` are canonically
the sections of `M` over `U`. -/
@[stacks 0G1V]
#check
  (structureModuleHomEquiv R U M :
    (structureModule R U ⟶ M) ≃ M.val.obj (op U))

end SheafOfModules.Localization
