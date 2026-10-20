/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.TrivialDeformation

/-!
# Trivial deformations and their functors

The trivial deformation is a chosen pullback along the coefficient section.
Its relative automorphisms and the isomorphism classes of lifts define functors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver

universe u

#check (AlgebraicGeometry.GroupoidsOver.trivialDeformationLift :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A),
    liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M))

#check (AlgebraicGeometry.GroupoidsOver.infTypeFunctor :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)), ModuleCat.{u} A ⥤ Type u)

#check (AlgebraicGeometry.GroupoidsOver.tangentTypeFunctor :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)), ModuleCat.{u} A ⥤ Type (u + 1))
