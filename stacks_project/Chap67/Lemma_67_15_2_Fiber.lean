/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ResidueFiber

/-!
# Residue-field fibers of étale module stalks

The étale local ring of an algebraic space at a geometric point is a local ring, and the
residue-field fiber of an `𝒪_X`-module is the tensor product of that residue field with the
étale module stalk.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped TensorProduct

universe u

#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing.instIsLocalRingAtGeometricPoint :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X),
    IsLocalRing (etaleLocalRing X xbar))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.fiber :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, GeometricPoint X → X.Modules → Type u)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.fiber_def :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) (F : X.Modules),
    Modules.fiber xbar F =
      IsLocalRing.ResidueField (etaleLocalRing X xbar) ⊗[etaleLocalRing X xbar]
        (stalkModuleCat xbar F))

