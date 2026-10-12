/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Points of pullbacks of algebraic spaces

Compatible scheme-valued points determine points of pullbacks of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Compatible scheme-valued points give compatible morphisms under Yoneda. -/
private theorem pullbackSchemePoint_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} {φ : U ⟶ X} (f : X' ⟶ X) {T : Over S}
    (x' : X'.left.functorOfPoints.obj (op T))
    (u : U.left.functorOfPoints.obj (op T))
    (h : φ.left.app (op T) u = f.left.app (op T) x') :
    (yonedaEquiv.symm u : ofOver T ⟶ U.left) ≫ φ.left =
      (yonedaEquiv.symm x' : ofOver T ⟶ X'.left) ≫ f.left :=
  sorry

/-- A compatible pair of a `T`-point of `X'` and a `T`-point of `U` determines a `T`-point
of `U' = pullback φ f`. -/
def pullbackSchemePoint {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    {φ : U ⟶ X} (f : X' ⟶ X) {T : Over S}
    (x' : X'.left.functorOfPoints.obj (op T))
    (u : U.left.functorOfPoints.obj (op T))
    (h : φ.left.app (op T) u = f.left.app (op T) x') :
    (pullback φ f).left.functorOfPoints.obj (op T) :=
  yonedaEquiv
    ((pullback.lift
          (yonedaEquiv.symm u : ofOver T ⟶ U.left)
          (yonedaEquiv.symm x' : ofOver T ⟶ X'.left)
          (pullbackSchemePoint_w f x' u h) :
        ofOver T ⟶ pullback ((Over.forget B).map φ) ((Over.forget B).map f)) ≫
      (PreservesPullback.iso (Over.forget B) φ f).inv :
      ofOver T ⟶ (pullback φ f).left)

/-- The `U`-component of `pullbackSchemePoint` recovers the original point of `U`. -/
theorem pullbackSchemePoint_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} {φ : U ⟶ X} (f : X' ⟶ X) {T : Over S}
    (x' : X'.left.functorOfPoints.obj (op T))
    (u : U.left.functorOfPoints.obj (op T))
    (h : φ.left.app (op T) u = f.left.app (op T) x') :
    (pullback.fst φ f).left.app (op T) (pullbackSchemePoint f x' u h) = u :=
  sorry

/-- The `X'`-component of `pullbackSchemePoint` recovers the original point of `X'`. -/
theorem pullbackSchemePoint_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} {φ : U ⟶ X} (f : X' ⟶ X) {T : Over S}
    (x' : X'.left.functorOfPoints.obj (op T))
    (u : U.left.functorOfPoints.obj (op T))
    (h : φ.left.app (op T) u = f.left.app (op T) x') :
    (pullback.snd φ f).left.app (op T) (pullbackSchemePoint f x' u h) = x' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
