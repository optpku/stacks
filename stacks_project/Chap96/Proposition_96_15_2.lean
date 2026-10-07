module

public import stacks_project.Chap96.Proposition_96_15_2_Coherator
public import stacks_project.Chap96.Proposition_96_15_2_Grothendieck
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.GroupoidsOver

universe u

section

/- Proposition 96.15.2 (1): for an algebraic stack `𝒳` over a scheme `S`, the category of
quasi-coherent `𝒪_𝒳`-modules is Grothendieck abelian. -/
@[stacks 0781] #check
  (QCoh.instIsGrothendieckAbelian :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], IsGrothendieckAbelian (QCoh X))

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

#check (IsGrothendieckAbelian.enoughInjectives : EnoughInjectives (QCoh X))

#check (IsGrothendieckAbelian.hasLimits (QCoh X) : HasLimits (QCoh X))

/- Proposition 96.15.2 (2): the inclusion `QCoh.inclusion X : QCoh X ⥤
RingedSite.ModuleCat.{u} (fppfRingedSite X)` has a right adjoint. -/
@[stacks 0781] #check
  (QCoh.inclusionIsLeftAdjoint :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], (QCoh.inclusion X).IsLeftAdjoint)

#check (QCoh.coherator :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    RingedSite.ModuleCat.{u} (fppfRingedSite X) ⥤ QCoh X)

variable (ℱ : QCoh X)

#check (inferInstance : IsIso
  ((Adjunction.ofIsLeftAdjoint (QCoh.inclusion X)).counit.app
    ((QCoh.inclusion X).obj ℱ)))

end
