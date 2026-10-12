/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_29_5_Comparison

/-!
# Canonical étale-local-ring comparison

The ring homomorphism is the existing inverse-image stalk construction used by
relative module flatness. Its specification below is quantified over every
compatible étale scheme square, independently of any chart.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- On any compatible étale scheme square, the local-ring map is the germ of the
structure-sheaf map on that square. This statement does not refer to a chosen atlas. -/
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
