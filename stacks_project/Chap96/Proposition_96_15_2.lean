/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.Grothendieck
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Additive
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.GroupoidsOver

universe u

section

/- Proposition 96.15.2 (1): for an algebraic stack `𝒳` over a scheme `S`, the category of
quasi-coherent `𝒪_𝒳`-modules is Grothendieck abelian. -/
@[stacks 0781] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.instIsGrothendieckAbelian :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      IsGrothendieckAbelian.{u} (QCoh X))

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

#check (IsGrothendieckAbelian.enoughInjectives : EnoughInjectives (QCoh X))

#check (IsGrothendieckAbelian.hasLimits (QCoh X) : HasLimitsOfSize.{u, u} (QCoh X))

/- Proposition 96.15.2 (2): the inclusion `QCoh.inclusion X : QCoh X ⥤
SheafOfModules.{u} (GroupoidsOver.structureSheaf X)` has a right adjoint. -/
@[stacks 0781] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.inclusionIsLeftAdjoint :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], (QCoh.inclusion X).IsLeftAdjoint)

#check ((QCoh.inclusion X).rightAdjoint :
  SheafOfModules.{u} (GroupoidsOver.structureSheaf X) ⥤ QCoh X)

#check (CategoryTheory.Adjunction.ofIsLeftAdjoint (QCoh.inclusion X) :
  QCoh.inclusion X ⊣ (QCoh.inclusion X).rightAdjoint)

#check (CategoryTheory.Adjunction.right_adjoint_additive
  (Adjunction.ofIsLeftAdjoint (QCoh.inclusion X)) :
    (QCoh.inclusion X).rightAdjoint.Additive)

variable (ℱ : QCoh X)

#check (inferInstance : IsIso
  ((Adjunction.ofIsLeftAdjoint (QCoh.inclusion X)).counit.app
    ((QCoh.inclusion X).obj ℱ)))

end
