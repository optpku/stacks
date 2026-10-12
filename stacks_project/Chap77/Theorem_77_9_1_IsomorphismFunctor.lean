/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# The isomorphism functor of a module morphism, as a functor of points over `S`

Situation 77.7.1 defines `F_iso` as a subterminal functor on schemes over `B`.
Algebraic-space structure and the closed immersion `F_iso ⟶ B` are expressed on
`(Over S)ᵒᵖ ⥤ Type u`, so this module records the corresponding subfunctor of
`B.functorOfPoints`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- The isomorphism functor of Situation 77.7.1, as a subfunctor of the functor of points of
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
  sorry

/-- The isomorphism functor of Situation 77.7.1, as a functor `(Over S)ᵒᵖ ⥤ Type u`. -/
def isomorphismOverSFunctor (u : ℱ ⟶ 𝒢) : (Over S)ᵒᵖ ⥤ Type u :=
  (isomorphismOverSSubfunctor f u).toFunctor

/-- `isomorphismOverSFunctor f u` is the underlying functor of
`isomorphismOverSSubfunctor f u`. -/
theorem isomorphismOverSFunctor_def (u : ℱ ⟶ 𝒢) :
    isomorphismOverSFunctor f u = (isomorphismOverSSubfunctor f u).toFunctor :=
  sorry

/-- The structural morphism `F_iso ⟶ B` of functors of points. -/
def isomorphismOverSFunctor_toB (u : ℱ ⟶ 𝒢) :
    isomorphismOverSFunctor f u ⟶ B.functorOfPoints :=
  (isomorphismOverSSubfunctor f u).ι

/-- `isomorphismOverSFunctor_toB f u` is the subfunctor inclusion of
`isomorphismOverSSubfunctor f u`. -/
theorem isomorphismOverSFunctor_toB_eq (u : ℱ ⟶ 𝒢) :
    isomorphismOverSFunctor_toB f u = (isomorphismOverSSubfunctor f u).ι :=
  sorry

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

/-- The functor of points of `space f u` is `isomorphismOverSFunctor f u`. -/
theorem space_functorOfPoints (u : ℱ ⟶ 𝒢)
    [IsAlgebraicSpace (isomorphismOverSFunctor f u)] :
    (space f u).functorOfPoints = isomorphismOverSFunctor f u :=
  sorry

/-- The structural morphism from the isomorphism space to `B`. -/
def toB (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (isomorphismOverSFunctor f u)] : space f u ⟶ B :=
  isomorphismOverSFunctor_toB f u

/-- `toB f u` is the functor-of-points morphism `isomorphismOverSFunctor_toB f u`. -/
theorem toB_eq (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (isomorphismOverSFunctor f u)] :
    toB f u = isomorphismOverSFunctor_toB f u :=
  sorry

/-- A morphism `a : ofOver T ⟶ B` factors through `toB f u` if and only if the pullback of
`u` along `a` is an isomorphism. -/
theorem factors_toB_iff (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (isomorphismOverSFunctor f u)]
    {T : Over S} (a : ofOver T ⟶ B) :
    (∃ b : ofOver T ⟶ space f u, b ≫ toB f u = a) ↔
      IsIso (baseChangeMap f a u) :=
  sorry

end isomorphismOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
