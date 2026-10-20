/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Map

/-!
# Étale local-ring maps on étale scheme squares
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- On any compatible étale scheme square, the étale local-ring map is the germ
of the structure-sheaf map on that square. -/
theorem etaleLocalRingMap_etaleSquare
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) (sq : EtaleSquare f)
    (lx : OverLift xbar sq.left) (ly : OverLift (xbar.map f) sq.right)
    (h : lx.hom ≫ sq.map = ly.hom) :
    (toSmallEtalePoint (xbar.map f)).toPresheafFiber sq.right ly (structureSheaf Y).obj ≫
        RingCat.ofHom (etaleLocalRingMap f xbar) =
      structureFMap_app sq ≫
        (toSmallEtalePoint xbar).toPresheafFiber sq.left lx (structureSheaf X).obj := sorry

end AlgebraicGeometry.AlgebraicSpace
