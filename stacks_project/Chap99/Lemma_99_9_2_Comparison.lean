module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Quot

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The Hilbert functor is naturally isomorphic to the Quot functor of the
structure sheaf for a finite-presentation morphism of algebraic spaces. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.quotIso :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f],
    Hilbert.hilbert f ≅ Quot.quot f (SheafOfModules.unit (structureSheaf X)))
