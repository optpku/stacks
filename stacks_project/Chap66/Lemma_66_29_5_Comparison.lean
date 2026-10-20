/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PullbackStalk
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing

/-!
# Compatibility view of the pullback-stalk comparison

A morphism of algebraic spaces induces functorial maps of étale local rings and a canonical
comparison from scalar extension of a module stalk to the stalk of its pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Modules ModuleCat

universe u

#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRingMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X),
    etaleLocalRing Y (xbar.map f) →+* etaleLocalRing X xbar)

#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRingMap_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (xbar : GeometricPoint X),
    etaleLocalRingMap (f ≫ g) xbar =
      (etaleLocalRingMap f xbar).comp (etaleLocalRingMap g (xbar.map f)))

#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRingMap_id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X),
    etaleLocalRingMap (𝟙 X) xbar = RingHom.id (etaleLocalRing X xbar))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackStalkComparison :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (G : Y.Modules)
    (xbar : GeometricPoint X),
    (extendScalars (etaleLocalRingMap f xbar)).obj (stalkModuleCat (xbar.map f) G) ⟶
      stalkModuleCat xbar ((pullback f).obj G))
