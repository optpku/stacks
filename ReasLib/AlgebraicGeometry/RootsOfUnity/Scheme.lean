/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import ReasLib.AlgebraicGeometry.RootsOfUnity.CoordinateRing
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec

/-!
# The affine scheme of roots of unity

This module constructs the integral affine scheme of roots of unity and identifies its
functor of points with roots of unity in global sections.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RootsOfUnity

/-- The affine roots-of-unity scheme over `Spec(ULift ℤ)`. -/
def overInt (n : ℕ) : Over (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  Scheme.OverSpec.affine
    (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (coordinateRing.{u} n)))

/-- The underlying scheme of `overInt n` is `Spec(coordinateRing n)`. -/
theorem overInt_left (n : ℕ) :
    (overInt.{u} n).left = Spec (CommRingCat.of (coordinateRing.{u} n)) := sorry

namespace HomOver

/-- Evaluation of a point of `overInt n` at its distinguished coordinate. -/
def value (n : ℕ) [NeZero n] (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : T ⟶ overInt.{u} n) : Γ(T.left, ⊤) :=
  (Scheme.OverSpec.ringHomOfHom
    (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (coordinateRing.{u} n))) f).right
      (generator.{u} n)

/-- Evaluation at the distinguished coordinate is an `n`th root of unity. -/
theorem value_pow (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : T ⟶ overInt.{u} n) : value n T f ^ n = 1 := sorry

/-- A point of `overInt n` determines an element of the roots-of-unity subgroup. -/
def root (n : ℕ) [NeZero n] (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : T ⟶ overInt.{u} n) : rootsOfUnity n Γ(T.left, ⊤) :=
  rootsOfUnity.mkOfPowEq (value n T f) (value_pow n T f)

/-- The underlying ring element of `root n T f` is distinguished-coordinate evaluation. -/
theorem root_coe (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : T ⟶ overInt.{u} n) : (root n T f).val.val = value n T f := sorry

/-- Evaluation at a chosen root annihilates the defining roots-of-unity relation. -/
private theorem pointEvaluation_descends (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (ζ : rootsOfUnity n Γ(T.left, ⊤)) :
    ∀ p ∈ relationIdeal n,
      Polynomial.eval₂RingHom (Scheme.OverSpec.baseRingHom T).hom ζ.val.val p = 0 := by
  intro p hp
  rcases (Ideal.mem_span_singleton.mp (by simpa [relationIdeal] using hp)) with ⟨q, rfl⟩
  simp [(mem_rootsOfUnity' n ζ.val).mp ζ.prop]

/-- The coordinate-ring map classified by a root of unity in global sections. -/
def ringHomOfRoot (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (ζ : rootsOfUnity n Γ(T.left, ⊤)) : coordinateRing.{u} n →+* Γ(T.left, ⊤) :=
  Ideal.Quotient.lift (relationIdeal n)
    (Polynomial.eval₂RingHom (Scheme.OverSpec.baseRingHom T).hom ζ.val.val)
    (by
      intro p hp
      rcases (Ideal.mem_span_singleton.mp (by simpa [relationIdeal] using hp)) with ⟨q, rfl⟩
      simp [(mem_rootsOfUnity' n ζ.val).mp ζ.prop])

/-- The classified coordinate-ring map sends the universal coordinate to the chosen root. -/
theorem ringHomOfRoot_generator (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (ζ : rootsOfUnity n Γ(T.left, ⊤)) :
    ringHomOfRoot n T ζ (generator.{u} n) = ζ.val.val := sorry

/-- The coordinate-ring map of a root is compatible with the maps from `ULift ℤ`. -/
private theorem pointMorphism_over (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (ζ : rootsOfUnity n Γ(T.left, ⊤)) :
    CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (coordinateRing.{u} n)) ≫
        CommRingCat.ofHom (ringHomOfRoot n T ζ) = Scheme.OverSpec.baseRingHom T :=
  CommRingCat.isInitial.hom_ext _ _

/-- The point of `overInt n` classified by a root of unity in global sections. -/
def ofRoot (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (ζ : rootsOfUnity n Γ(T.left, ⊤)) : T ⟶ overInt.{u} n :=
  Scheme.OverSpec.homOfRingHom
    (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (coordinateRing.{u} n)))
    (Under.homMk (CommRingCat.ofHom (ringHomOfRoot n T ζ))
      (CommRingCat.isInitial.hom_ext _ _))

/-- Reconstructing a point from its distinguished-coordinate root is the identity. -/
theorem ofRoot_root (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : T ⟶ overInt.{u} n) : ofRoot n T (root n T f) = f := sorry

/-- Evaluating the point classified by a root recovers that root. -/
theorem root_ofRoot (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (ζ : rootsOfUnity n Γ(T.left, ⊤)) : root n T (ofRoot n T ζ) = ζ := sorry

/-- Points of `overInt n` are canonically equivalent to roots of unity in global sections. -/
def equiv (n : ℕ) [NeZero n] (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (T ⟶ overInt.{u} n) ≃ rootsOfUnity n Γ(T.left, ⊤) where
  toFun := root n T
  invFun := ofRoot n T
  left_inv := ofRoot_root n T
  right_inv := root_ofRoot n T

/-- The forward map of `equiv` is distinguished-coordinate evaluation. -/
theorem equiv_apply (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : T ⟶ overInt.{u} n) : equiv n T f = root n T f := sorry

/-- The affine point equivalence is natural under precomposition over `Spec(ULift ℤ)`. -/
theorem equiv_naturality (n : ℕ) [NeZero n]
    {T T' : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (g : T' ⟶ T)
    (f : T ⟶ overInt.{u} n) :
    equiv n T' (g ≫ f) =
      restrictRootsOfUnity (Scheme.Γ.map g.left.op).hom n (equiv n T f) := sorry

end HomOver
end AlgebraicGeometry.RootsOfUnity
