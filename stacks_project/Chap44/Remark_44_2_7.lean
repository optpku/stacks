/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.Representability
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Remark 44.2.7 (1): if `X` is quasi-affine, every finite family of points in one
fiber of `X ⟶ S` is contained in an affine open of `X`. -/
@[stacks 0B9B] #check
  (AlgebraicGeometry.Hilbert.fiberPointsContainedInAffineOpen_of_isQuasiAffine :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (d : ℕ) [X.left.IsQuasiAffine],
      AlgebraicGeometry.Hilbert.FiberPointsContainedInAffineOpen X d)

/- Remark 44.2.7 (2): if `X ⟶ S` is quasi-affine, every finite family of points
in one fiber is contained in an affine open of `X`. -/
@[stacks 0B9B] #check
  (AlgebraicGeometry.Hilbert.fiberPointsContainedInAffineOpen_of_quasiAffineHom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (d : ℕ),
      AlgebraicGeometry.QuasiAffineHom X.hom →
      AlgebraicGeometry.Hilbert.FiberPointsContainedInAffineOpen X d)

/- Remark 44.2.7 (3): if `X ⟶ S` is quasi-projective, every finite family of
points in one fiber is contained in an affine open of `X`. -/
@[stacks 0B9B] #check
  (AlgebraicGeometry.Hilbert.fiberPointsContainedInAffineOpen_of_quasiProjective :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (d : ℕ)
      [AlgebraicGeometry.QuasiProjective X.hom],
      AlgebraicGeometry.Hilbert.FiberPointsContainedInAffineOpen X d)

/- Remark 44.2.7 (4): if `X ⟶ S` is locally projective, every finite family of
points in one fiber is contained in an affine open of `X`. -/
@[stacks 0B9B] #check
  (AlgebraicGeometry.Hilbert.fiberPointsContainedInAffineOpen_of_locallyProjective :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (d : ℕ)
      [AlgebraicGeometry.LocallyProjective X.hom],
      AlgebraicGeometry.Hilbert.FiberPointsContainedInAffineOpen X d)

/- Remark 44.2.7 (5): if `X` admits an ample invertible module, every finite family
of points in one fiber of `X ⟶ S` is contained in an affine open of `X`. -/
@[stacks 0B9B] #check
  (AlgebraicGeometry.Hilbert.fiberPointsContainedInAffineOpen_of_hasAmpleInvertibleModule :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (d : ℕ),
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X.left →
        AlgebraicGeometry.Hilbert.FiberPointsContainedInAffineOpen X d)

/- Remark 44.2.7 (6): the existence of a relatively ample module for `X ⟶ S`
ensures that every finite family of points in one fiber lies in an affine open of `X`. -/
@[stacks 0B9B] #check
  (AlgebraicGeometry.Hilbert.fiberPointsContainedInAffineOpen_of_exists_relativelyAmple :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (d : ℕ),
      (∃ L : X.left.Modules, AlgebraicGeometry.RelativelyAmple X.hom L) →
        AlgebraicGeometry.Hilbert.FiberPointsContainedInAffineOpen X d)

/- Remark 44.2.7 (7): the existence of a relatively very ample module for `X ⟶ S`
ensures that every finite family of points in one fiber lies in an affine open of `X`. -/
@[stacks 0B9B] #check
  (AlgebraicGeometry.Hilbert.fiberPointsContainedInAffineOpen_of_exists_relativelyVeryAmple :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (d : ℕ),
      (∃ L : X.left.Modules, AlgebraicGeometry.RelativelyVeryAmple X.hom L) →
        AlgebraicGeometry.Hilbert.FiberPointsContainedInAffineOpen X d)

#check
  (AlgebraicGeometry.Hilbert.functor_isRepresentable_of_fiber_points_contained_in_affineOpen :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (d : ℕ)
      [AlgebraicGeometry.Hilbert.FiberPointsContainedInAffineOpen X d],
      (AlgebraicGeometry.Hilbert.functor X d).IsRepresentable)
