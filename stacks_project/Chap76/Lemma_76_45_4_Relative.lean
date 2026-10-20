module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsMPseudoCoherentOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f], ModuleDerived X → ℤ → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPseudoCoherentOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f], ModuleDerived X → Prop)
