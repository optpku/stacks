/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation

/-!
# Infinitesimal and tangent functors of a deformation object

Under the strong Rim-Schlessinger condition, infinitesimal automorphisms and
lift classes define linear functors, with comparison isomorphisms and tangent actions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver

universe u

#check (AlgebraicGeometry.GroupoidsOver.infFunctor.instModuleLinear :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)), ModuleLinear (A : Type u) (infFunctor x))

#check (AlgebraicGeometry.GroupoidsOver.infIso :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA),
    (infFunctor x).obj (kernelObj fA) ≅ ModuleCat.of A (infinitesimalAut x'))

#check (AlgebraicGeometry.GroupoidsOver.tangentFunctor.instModuleLinear :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)), ModuleLinear (A : Type u) (tangentFunctor x))

#check (AlgebraicGeometry.GroupoidsOver.tangentForget :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A),
    ((tangentFunctor x).obj M : Type (u + 1)) ≃
      lifts x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M))

#check (AlgebraicGeometry.GroupoidsOver.tangentForget_bijective :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A),
    Function.Bijective (tangentForget x M))

#check (AlgebraicGeometry.GroupoidsOver.tangentAction :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)),
    (tangentFunctor x).obj (kernelObj fA) → lifts x fA hfA → lifts x fA hfA)

#check (AlgebraicGeometry.GroupoidsOver.tangentAction_zero :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (ξ : lifts x fA hfA),
    tangentAction x (0 : (tangentFunctor x).obj (kernelObj fA)) ξ = ξ)

#check (AlgebraicGeometry.GroupoidsOver.tangentAction_add :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA))
    (s t : (tangentFunctor x).obj (kernelObj fA)) (ξ : lifts x fA hfA),
    tangentAction x (s + t) ξ = tangentAction x s (tangentAction x t ξ))

#check (AlgebraicGeometry.GroupoidsOver.tangentAction_simplyTransitive :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) [Nonempty (lifts x fA hfA)]
    (ξ η : lifts x fA hfA),
    ∃! t : (tangentFunctor x).obj (kernelObj fA), tangentAction x t ξ = η)
