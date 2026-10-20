module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation.ChangeOfBase

/-!
# Representable change-of-base identifications

The functor-of-points identifications for representable algebraic spaces and the
transport of their presentations are supplied by the shared change-of-base owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Viewing the representable algebraic space of `X` over `S` along `g` recovers the
representable algebraic space of `j(X)`. -/
def extendBase_ofOver_functorOfPoints {S S' : Scheme.{u}} (g : S ⟶ S') (X : Over S) :
    (extendBase g (ofOver X)).functorOfPoints ≅
      (ofOver ((Over.map g).obj X)).functorOfPoints :=
  extendBasePresheafYonedaIso g X

/-- Base changing the representable algebraic space of `X'` along `g` recovers the
representable algebraic space of `S ×_{S'} X'`. -/
def baseChange_ofOver_functorOfPoints {S S' : Scheme.{u}} (g : S ⟶ S')
    (X' : Over S') :
    (baseChange g (ofOver X')).functorOfPoints ≅
      (ofOver ((Over.pullback g).obj X')).functorOfPoints :=
  baseChangePresheafYonedaIso g X'

#check (AlgebraicGeometry.AlgebraicSpace.Presentation.extendBase :
  ∀ {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S'),
    Presentation F → Presentation (AlgebraicSpace.extendBase g F))

#check (AlgebraicGeometry.AlgebraicSpace.Presentation.baseChange :
  ∀ {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S'),
    Presentation F' → Presentation (AlgebraicSpace.baseChange g F'))

end AlgebraicGeometry.AlgebraicSpace
