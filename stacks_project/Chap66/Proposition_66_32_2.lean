/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Coherator
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Grothendieck
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

/- Proposition 66.32.2 (1): for an algebraic space `X` over a scheme `S`, the category of
quasi-coherent `𝒪_X`-modules is Grothendieck abelian. -/
@[stacks 077V] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.instIsGrothendieckAbelian :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), IsGrothendieckAbelian (QCoh X))

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

#check (CategoryTheory.IsGrothendieckAbelian.enoughInjectives : EnoughInjectives (QCoh X))

#check (CategoryTheory.IsGrothendieckAbelian.hasLimits (QCoh X) : HasLimits (QCoh X))

/- Proposition 66.32.2 (2): the inclusion `QCoh.inclusion X : QCoh X ⥤ Modules X` has a right
adjoint. -/
@[stacks 077V] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.inclusionIsLeftAdjoint :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), (QCoh.inclusion X).IsLeftAdjoint)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.coherator :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), X.Modules ⥤ QCoh X)

variable (ℱ : QCoh X)

#check (CategoryTheory.Adjunction.isIso_counit_app_of_iso
  (AlgebraicGeometry.AlgebraicSpace.QCoh.coheratorAdjunction X)
  (Iso.refl ((QCoh.inclusion X).obj ℱ)) :
  IsIso ((AlgebraicGeometry.AlgebraicSpace.QCoh.coheratorAdjunction X).counit.app
    ((QCoh.inclusion X).obj ℱ)))

end
