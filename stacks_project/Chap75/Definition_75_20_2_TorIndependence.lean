/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence
public import stacks_project.Chap66.Lemma_66_29_5_Comparison

/-!
# Tor independence of algebraic spaces

Two algebraic spaces over a common algebraic space `B` are Tor independent when their
étale local rings at every pair of compatible geometric points are Tor independent over
the corresponding étale local ring of `B`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.AlgebraicSpace.torIndependentOver_iff :
  ∀ {B : AlgebraicSpace S} (X Y : Over B),
    TorIndependentOver X Y ↔
      let X₀ := X.left
      let Y₀ := Y.left
      let f := X.hom
      let g := Y.hom
      ∀ (xbar : GeometricPoint X₀) (ybar : GeometricPoint Y₀) (h : xbar.map f = ybar.map g),
        ModuleCat.Tor.IsIndependent
          ((ModuleCat.restrictScalars (etaleLocalRingMap f xbar)).obj
            (ModuleCat.of (etaleLocalRing X₀ xbar) (etaleLocalRing X₀ xbar)))
          (h.symm ▸
            (ModuleCat.restrictScalars (etaleLocalRingMap g ybar)).obj
              (ModuleCat.of (etaleLocalRing Y₀ ybar) (etaleLocalRing Y₀ ybar))))

#check (AlgebraicGeometry.AlgebraicSpace.TorIndependentOver.isIndependent :
  ∀ {B : AlgebraicSpace S} {X Y : Over B}
    (hXY : TorIndependentOver X Y)
    (xbar : GeometricPoint X.left) (ybar : GeometricPoint Y.left)
    (hxy : xbar.map X.hom = ybar.map Y.hom),
    ModuleCat.Tor.IsIndependent
      ((ModuleCat.restrictScalars (etaleLocalRingMap X.hom xbar)).obj
        (ModuleCat.of (etaleLocalRing X.left xbar) (etaleLocalRing X.left xbar)))
      (hxy.symm ▸
        (ModuleCat.restrictScalars (etaleLocalRingMap Y.hom ybar)).obj
          (ModuleCat.of (etaleLocalRing Y.left ybar) (etaleLocalRing Y.left ybar))))

end AlgebraicGeometry.AlgebraicSpace
