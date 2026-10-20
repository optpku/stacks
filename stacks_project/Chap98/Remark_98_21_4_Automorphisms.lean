/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalHom
import StacksCheckRecall

/-!
# Automorphisms of lifts along a first-order thickening

Infinitesimal automorphisms act on morphisms of lifts. The canonical
identifications with the infinitesimal module identify the two operations,
giving a simply transitive action whenever the Hom-set is nonempty.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver

universe u

/- Remark 98.21.4 (Automorphisms). The canonical infinitesimal module acts
simply transitively on every nonempty Hom-set of lifts. -/
@[stacks 07YB] #check (AlgebraicGeometry.GroupoidsOver.infHomAct_simplyTransitive :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [HasStrongRimSchlessinger X] [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    [Nonempty (x' ⟶ x'')] (φ ψ : x' ⟶ x''),
    ∃! t : (infFunctor x).obj (kernelObj fA), infHomAct x x' x'' t φ = ψ)

#check (AlgebraicGeometry.GroupoidsOver.infHomComp_val :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    {x : X.p.Fiber (Over.mk σA)} (x' x'' : liftCat x fA hfA)
    (α : infinitesimalAut x') (φ : x' ⟶ x'') (β : infinitesimalAut x''),
    (infHomComp x' x'' α φ β).val = α.val.hom ≫ φ.val ≫ β.val.hom)

#check (AlgebraicGeometry.GroupoidsOver.infHomLeftAct_simplyTransitive :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [HasStrongRimSchlessinger X] [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    [Nonempty (x' ⟶ x'')] (φ ψ : x' ⟶ x''),
    ∃! α : infinitesimalAut x', infHomLeftAct x' x'' α φ = ψ)

#check (AlgebraicGeometry.GroupoidsOver.infHomRightAct_simplyTransitive :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [HasStrongRimSchlessinger X] [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    [Nonempty (x' ⟶ x'')] (φ ψ : x' ⟶ x''),
    ∃! β : infinitesimalAut x'', infHomRightAct x' x'' φ β = ψ)

#check (AlgebraicGeometry.GroupoidsOver.infHom_left_eq_right :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    [HasStrongRimSchlessinger X] [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    (t : (infFunctor x).obj (kernelObj fA)) (φ : x' ⟶ x''),
    infHomLeftAct x' x'' ((infIso x x').hom t) φ =
      infHomRightAct x' x'' φ ((infIso x x'').hom t))
