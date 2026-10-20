module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Restriction

/-! # Étale restriction of derived quasi-coherent modules -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Étale restriction of a derived object with quasi-coherent cohomology, with
underlying object given by the derived restriction of modules. -/
def restrict {S : Scheme.{u}} {V X : AlgebraicSpace S} (f : V ⟶ X) [Etale f]
    (E : DerivedQCoh X) : DerivedQCoh V where
  obj := (Modules.restrictFunctorDerived f).obj E.obj
  property := sorry

/-- The underlying derived module of étale restriction is the derived restriction
of the underlying module. -/
theorem restrict_obj {S : Scheme.{u}} {V X : AlgebraicSpace S} (f : V ⟶ X) [Etale f]
    (E : DerivedQCoh X) :
    (restrict f E).obj = (Modules.restrictFunctorDerived f).obj E.obj :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
