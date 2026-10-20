module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalAutomorphisms

/-!
# Relative infinitesimal automorphisms

The group of automorphisms of a lift fixing its source arrow is the kernel
of restriction to the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver

universe u

#check (AlgebraicGeometry.GroupoidsOver.infinitesimalAut :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {fA : A' ⟶ A}
    {hfA : Spec.map fA ≫ σA' = σA} (x' : liftCat x fA hfA),
    Subgroup (Aut x'.codomain))

#check (AlgebraicGeometry.GroupoidsOver.restrictAut :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {fA : A' ⟶ A}
    {hfA : Spec.map fA ≫ σA' = σA} (x' : liftCat x fA hfA),
    Aut x'.codomain →* Aut x)
