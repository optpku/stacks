/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.GlobalSections.Obstruction

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Example 98.22.3. The category fibred in groupoids of global sections of a quasi-coherent
module flat over a Noetherian affine base has the boundary obstruction theory. -/
@[stacks 07YH] #check (AlgebraicGeometry.GroupoidsOver.GlobalSections.obstructionTheory :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of Λ))
    (F : W.Modules) [SheafOfModules.IsQuasicoherent F],
    Scheme.Modules.flatOver F w →
      GroupoidsOver.ObstructionTheory (GroupoidsOver.GlobalSections.toGroupoids w F))

#check (AlgebraicGeometry.GroupoidsOver.GlobalSections.exists_lift_iff_obstructionClass_eq_zero :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of Λ))
    (F : W.Modules) [SheafOfModules.IsQuasicoherent F]
    (hflat : Scheme.Modules.flatOver F w)
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] [(algebraMap A' A).IsSquareZeroExtension]
    (x : Γ(GroupoidsOver.GlobalSections.affineModulePullback w F A, ⊤)),
    (∃ y : Γ(GroupoidsOver.GlobalSections.affineModulePullback w F A', ⊤),
      (GroupoidsOver.GlobalSections.sectionsFunctor w F).map
        (GroupoidsOver.GlobalSections.specOverMap Λ A A').op y = x) ↔
      GroupoidsOver.GlobalSections.obstructionClass w F A A' hflat x = 0)

