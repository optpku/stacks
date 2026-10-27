/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map

/-!
# The isomorphism functor of a module morphism, as a functor of points over `S`

For a morphism of quasi-coherent modules on an algebraic space over `B`, the
isomorphism subfunctor of `B.functorOfPoints` records the morphisms from schemes
over `S` to `B` along which the module morphism becomes invertible.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- The isomorphism functor of a module morphism, as a subfunctor of the functor of points of
`B` on schemes over `S`: a morphism `ofOver T ⟶ B` lies in `F_iso` precisely when the
pullback of `u` along it is an isomorphism. -/
def isomorphismOverSSubfunctor (u : ℱ ⟶ 𝒢) : Subfunctor B.functorOfPoints where
  obj T := {φ | IsIso (baseChangeMap f (yonedaEquiv.symm φ) u)}
  map := sorry

/-- Membership in the `(Sch/S)` isomorphism subfunctor is invertibility of the pullback of `u`
along the corresponding morphism `ofOver T ⟶ B`. -/
theorem mem_isomorphismOverSSubfunctor (u : ℱ ⟶ 𝒢) {T : Over S}
    (φ : B.functorOfPoints.obj (op T)) :
    φ ∈ (isomorphismOverSSubfunctor f u).obj (op T) ↔
      IsIso (baseChangeMap f (yonedaEquiv.symm φ) u) :=
  Iff.rfl

/-- The isomorphism functor of a module morphism, as a functor `(Over S)ᵒᵖ ⥤ Type u`. -/
def isomorphismOverSFunctor (u : ℱ ⟶ 𝒢) : (Over S)ᵒᵖ ⥤ Type u :=
  (isomorphismOverSSubfunctor f u).toFunctor

/-- The structural morphism `F_iso ⟶ B` of functors of points. -/
def isomorphismOverSFunctor_toB (u : ℱ ⟶ 𝒢) :
    isomorphismOverSFunctor f u ⟶ B.functorOfPoints :=
  (isomorphismOverSSubfunctor f u).ι

/-- A scheme `T` over `S` has an `F_iso`-point if and only if some morphism `ofOver T ⟶ B`
makes `u` an isomorphism after base change. -/
theorem isomorphismOverSFunctor_nonempty_iff (u : ℱ ⟶ 𝒢) (T : Over S) :
    Nonempty ((isomorphismOverSFunctor f u).obj (op T)) ↔
      ∃ a : ofOver T ⟶ B, IsIso (baseChangeMap f a u) :=
  sorry

namespace isomorphismOverSFunctor

/-- The algebraic space representing the `(Sch/S)` isomorphism functor, when that functor is
an algebraic space. -/
def space (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (isomorphismOverSFunctor f u)] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (isomorphismOverSFunctor f u)

/-- The structural morphism from the isomorphism space to `B`. -/
def toB (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (isomorphismOverSFunctor f u)] : space f u ⟶ B :=
  isomorphismOverSFunctor_toB f u

/-- A morphism `a : ofOver T ⟶ B` factors through `toB f u` if and only if the pullback of
`u` along `a` is an isomorphism. -/
theorem factors_toB_iff (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (isomorphismOverSFunctor f u)]
    {T : Over S} (a : ofOver T ⟶ B) :
    (∃ b : ofOver T ⟶ space f u, b ≫ toB f u = a) ↔
      IsIso (baseChangeMap f a u) :=
  sorry

end isomorphismOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
