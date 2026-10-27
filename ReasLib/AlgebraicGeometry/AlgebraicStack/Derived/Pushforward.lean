/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy

/-! # Unbounded derived direct image of fppf modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver ComplexShape
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

-- Local instance justification (defeq pin): the homotopy localization must use the Abelian and induced additive structures of the fppf module presentation in ModuleDerived.
attribute [local instance 2000] GroupoidsOver.fppfModulesAbelian
  Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms fppfModulesHasDerivedCategory

-- Local instance justification (defeq pin): ModuleDerived uses this standard localization through fppfModulesHasDerivedCategory, at the same module-category universe.
attribute [local instance 1900] HasDerivedCategory.standard

-- Local instance justification (defeq pin): homotopy-to-derived direct image must select the canonical additivity certificate for the concrete fppf module direct image.
attribute [local instance 2000] instFppfModulePushforwardAdditive

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

set_option backward.isDefEq.respectTransparency false in
/-- Fppf module direct image admits a total right derived functor at homotopy
quasi-isomorphisms. -/
instance fppfModulePushforwardHasRightDerived (f : X ⟶ Y) :
    (Functor.Homotopy.toDerived (fppfModulePushforward f)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (fppfModules X) (up ℤ)) := sorry

set_option backward.isDefEq.respectTransparency false in
/-- The canonical unbounded derived direct image of fppf modules. -/
abbrev moduleDerivedPushforward (f : X ⟶ Y) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  @Functor.RightDerived.Homotopy.functor
    (fppfModules X) inferInstance (GroupoidsOver.fppfModulesAbelian X)
      (fppfModulesHasDerivedCategory X)
    (fppfModules Y) inferInstance (GroupoidsOver.fppfModulesAbelian Y)
      (fppfModulesHasDerivedCategory Y)
    (fppfModulePushforward f) (instFppfModulePushforwardAdditive f)
      (fppfModulePushforwardHasRightDerived f)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison from homotopy-level fppf direct image to its
unbounded right derived functor. -/
abbrev moduleDerivedPushforwardUnit (f : X ⟶ Y) :
    Functor.Homotopy.toDerived (fppfModulePushforward f) ⟶
      (DerivedCategory.Qh : HomotopyCategory (fppfModules X) (up ℤ) ⥤ ModuleDerived X) ⋙
        moduleDerivedPushforward f :=
  @Functor.RightDerived.Homotopy.unit
    (fppfModules X) inferInstance (GroupoidsOver.fppfModulesAbelian X)
      (fppfModulesHasDerivedCategory X)
    (fppfModules Y) inferInstance (GroupoidsOver.fppfModulesAbelian Y)
      (fppfModulesHasDerivedCategory Y)
    (fppfModulePushforward f) (instFppfModulePushforwardAdditive f)
      (fppfModulePushforwardHasRightDerived f)

set_option backward.isDefEq.respectTransparency false in
/-- Unbounded fppf derived direct image satisfies the right-derived universal property. -/
instance moduleDerivedPushforwardIsRightDerived (f : X ⟶ Y) :
    (moduleDerivedPushforward f).IsRightDerivedFunctor (moduleDerivedPushforwardUnit f)
      (HomotopyCategory.quasiIso (fppfModules X) (up ℤ)) :=
  @Functor.RightDerived.Homotopy.isRightDerived
    (fppfModules X) inferInstance (GroupoidsOver.fppfModulesAbelian X)
      (fppfModulesHasDerivedCategory X)
    (fppfModules Y) inferInstance (GroupoidsOver.fppfModulesAbelian Y)
      (fppfModulesHasDerivedCategory Y)
    (fppfModulePushforward f) (instFppfModulePushforwardAdditive f)
      (fppfModulePushforwardHasRightDerived f)

/-- Unbounded fppf derived direct image preserves locally quasi-coherent
cohomology with flat base change. -/
def mapsDerivedLQCohFbc (f : X ⟶ Y) : Prop :=
  DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) ≤
    (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc Y)).inverseImage
      (moduleDerivedPushforward f)

/-- Preservation of locally quasi-coherent cohomology with flat base change is
equivalent to the corresponding objectwise condition on derived direct image. -/
theorem mapsDerivedLQCohFbc_iff (f : X ⟶ Y) :
    mapsDerivedLQCohFbc f ↔
      ∀ E : ModuleDerived X,
        DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) E →
          DerivedCategory.cohomologyIn (FppfModules.lqcohFbc Y)
            ((moduleDerivedPushforward f).obj E) := sorry

end AlgebraicGeometry.AlgebraicStack
