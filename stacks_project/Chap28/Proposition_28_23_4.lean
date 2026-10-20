module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Grothendieck
import StacksCheckRecall

@[expose] public section

universe u

section

/- Proposition 28.23.4: for every scheme `X`, the category of quasicoherent modules on `X`
is Grothendieck abelian. -/
@[stacks 077P] #check
  (AlgebraicGeometry.Scheme.QCoh.instIsGrothendieckAbelian :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      CategoryTheory.IsGrothendieckAbelian (AlgebraicGeometry.Scheme.QCoh X))

variable (X : AlgebraicGeometry.Scheme.{u})

#check (CategoryTheory.IsGrothendieckAbelian.enoughInjectives :
  CategoryTheory.EnoughInjectives (AlgebraicGeometry.Scheme.QCoh X))

#check (CategoryTheory.IsGrothendieckAbelian.hasLimits
  (AlgebraicGeometry.Scheme.QCoh X) :
  CategoryTheory.Limits.HasLimits (AlgebraicGeometry.Scheme.QCoh X))

#check (AlgebraicGeometry.Scheme.QCoh.inclusionIsLeftAdjoint :
  ∀ X : AlgebraicGeometry.Scheme.{u},
    (AlgebraicGeometry.Scheme.QCoh.inclusion X).IsLeftAdjoint)

variable (ℱ : AlgebraicGeometry.Scheme.QCoh X)

#check (inferInstance : CategoryTheory.IsIso
  ((CategoryTheory.Adjunction.ofIsLeftAdjoint
    (AlgebraicGeometry.Scheme.QCoh.inclusion X)).counit.app
      ((AlgebraicGeometry.Scheme.QCoh.inclusion X).obj ℱ)))

end
