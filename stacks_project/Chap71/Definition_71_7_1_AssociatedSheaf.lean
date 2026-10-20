/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier

/-! # Associated sheaves and universe lifting of module morphisms

The mathematical owners provide the associated divisor sheaves and the
sectionwise universe lifting of module morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.associatedSheaf :
    {S : Scheme.{u}} → {D X : AlgebraicSpace S} →
      (i : D ⟶ X) → [IsEffectiveCartierDivisor i] → X.Modules)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.liftModuleMap :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → {F G : X.Modules} →
      (F ⟶ G) → (Modules.liftModule F ⟶ Modules.liftModule G))
