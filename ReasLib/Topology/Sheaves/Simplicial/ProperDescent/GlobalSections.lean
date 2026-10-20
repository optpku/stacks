/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.GlobalSections
public import ReasLib.Topology.Sheaves.Simplicial.ProperDescent.Derived

/-!
# Derived global sections and proper hypercoverings

Proper hypercoverings of Hausdorff locally compact spaces preserve bounded-below
derived global sections under the canonical augmentation comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u

namespace LCCat

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
variable [HasSheafify (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X.obj)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
variable [HasGlobalSectionsFunctor (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
variable [HasGlobalSectionsFunctor (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}]
variable [(augmentationPushforward (toTopCatAugmentation a)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}))]
variable [(Sheaf.Γ (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}))]
variable [(Sheaf.Γ (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}))]

/-- For a proper hypercovering of a Hausdorff locally compact space, the canonical
comparison from derived global sections to those of the augmentation inverse image
is an isomorphism at every bounded-below complex of abelian sheaves. -/
theorem rGammaPullbackComparison_app_isIso (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})) :
    IsIso ((rGammaPullbackComparison (toTopCatAugmentation a)).app K) :=
  sorry

/-- The comparison `RΓ(X, -) ⟶ a⁻¹ ⋙ RΓ(U_Zar, -)` is an isomorphism of functors
on `D⁺(X)`. -/
theorem rGammaPullbackComparison_isIso (ha : IsProperHypercovering a) :
    IsIso (rGammaPullbackComparison (toTopCatAugmentation a)) :=
  sorry

end LCCat

end
