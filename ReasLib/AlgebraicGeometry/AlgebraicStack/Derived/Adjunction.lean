/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Pushforward
public import ReasLib.CategoryTheory.Adjunction.Derived.ExactLeft

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver ComplexShape
open scoped Bicategory

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

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

/-- Exact inverse image preserves the composite right-derived universal property
for canonical fppf module direct image. -/
instance fppfModuleDerivedAdjunctionRightLeft (f : X ⟶ Y) :
    (moduleDerivedPushforward f ⋙ fppfModuleDerivedInverseImage f).IsRightDerivedFunctor
      (Adjunction.Derived.ExactLeft.rightLeftUnit
        (fppfModuleInverseImageExact f) (fppfModulePushforward f))
      (HomologicalComplex.quasiIso (fppfModules X) (up ℤ)) := sorry

/-- Derived inverse image of fppf modules is left adjoint to canonical unbounded
derived direct image. -/
def fppfModuleDerivedAdjunction (f : X ⟶ Y) :
    fppfModuleDerivedInverseImage f ⊣ moduleDerivedPushforward f :=
  Adjunction.Derived.ExactLeft.adjunction (fppfModuleInverseImageExact f)
    (fppfModulePushforward f) (fppfModuleAdjunction f)
    (fppfModuleDerivedAdjunctionRightLeft f)

end AlgebraicGeometry.AlgebraicStack
