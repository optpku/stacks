/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Proposition_66_32_2_Coherator
public import stacks_project.Chap66.Proposition_66_32_2_Grothendieck
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

/- Proposition 66.32.2 (1): for an algebraic space `X` over a scheme `S`, the category of
quasi-coherent `𝒪_X`-modules is Grothendieck abelian. -/
@[stacks 077V] #check
  (QCoh.instIsGrothendieckAbelian :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), IsGrothendieckAbelian (QCoh X))

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

#check (IsGrothendieckAbelian.enoughInjectives : EnoughInjectives (QCoh X))

#check (IsGrothendieckAbelian.hasLimits (QCoh X) : HasLimits (QCoh X))

/- Proposition 66.32.2 (2): the inclusion `QCoh.inclusion X : QCoh X ⥤ Modules X` has a right
adjoint. -/
@[stacks 077V] #check
  (QCoh.inclusionIsLeftAdjoint :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), (QCoh.inclusion X).IsLeftAdjoint)

#check (QCoh.coherator : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), X.Modules ⥤ QCoh X)

variable (ℱ : QCoh X)

#check (inferInstance : IsIso
  ((Adjunction.ofIsLeftAdjoint (QCoh.inclusion X)).counit.app
    ((QCoh.inclusion X).obj ℱ)))

end
