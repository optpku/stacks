/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap77.«77_7_8_1_Flattening»

/-!
# Universal flattening of a quasi-coherent module on an algebraic space

The flattening functor of Situation 77.7.8 is viewed as a subfunctor of the functor of
points of `Y` on schemes over `S`. The universal flattening of a quasi-coherent module
exists when that `(Sch/S)ᵒᵖ` functor is an algebraic space.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The structure sheaf of an algebraic space, viewed as a module over itself, is
quasi-coherent. -/
instance instIsQuasicoherent_unit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).IsQuasicoherent :=
  sorry

namespace Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- The flattening functor of Situation 77.7.8, as a subfunctor of the functor of points of
`Y` on schemes over `S`: a morphism `ofOver T ⟶ Y` lies in `F_flat` precisely when the
pullback of `ℱ` along it is flat over `T`. -/
def overSSubfunctor : Subfunctor Y.functorOfPoints where
  obj T := {φ | isFlat f ℱ (SchemeOver.mk (yonedaEquiv.symm φ))}
  map := sorry

/-- Membership in the `(Sch/S)` flattening subfunctor is relative flatness of the pullback
of `ℱ` along the corresponding morphism `ofOver T ⟶ Y`. -/
theorem mem_overSSubfunctor {T : Over S} (φ : Y.functorOfPoints.obj (op T)) :
    φ ∈ (overSSubfunctor f ℱ).obj (op T) ↔
      isFlat f ℱ (SchemeOver.mk (yonedaEquiv.symm φ)) :=
  sorry

/-- The flattening functor of Situation 77.7.8, as a functor `(Over S)ᵒᵖ ⥤ Type u`. -/
def overSFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (overSSubfunctor f ℱ).toFunctor

/-- `overSFunctor f ℱ` is the underlying functor of `overSSubfunctor f ℱ`. -/
theorem overSFunctor_def : overSFunctor f ℱ = (overSSubfunctor f ℱ).toFunctor :=
  sorry

/-- The structural morphism `F_flat ⟶ Y` of functors of points. -/
def overSFunctor_toY : overSFunctor f ℱ ⟶ Y.functorOfPoints :=
  (overSSubfunctor f ℱ).ι

/-- `overSFunctor_toY f ℱ` is the subfunctor inclusion of `overSSubfunctor f ℱ`. -/
theorem overSFunctor_toY_eq : overSFunctor_toY f ℱ = (overSSubfunctor f ℱ).ι :=
  sorry

/-- A scheme `T` over `S` has an `F_flat`-point if and only if some morphism `ofOver T ⟶ Y`
flattens `ℱ`. -/
theorem overSFunctor_nonempty_iff (T : Over S) :
    Nonempty ((overSFunctor f ℱ).obj (op T)) ↔
      ∃ a : ofOver T ⟶ Y, isFlat f ℱ (SchemeOver.mk a) :=
  sorry

/-- The universal flattening of a quasi-coherent `𝒪_X`-module exists when the `(Sch/S)`
flattening functor is an algebraic space. -/
abbrev HasUniversalFlattening : Prop :=
  IsAlgebraicSpace (overSFunctor f ℱ)

/-- Existence of a universal flattening of `ℱ` is the algebraic-space condition on
`overSFunctor f ℱ`. -/
theorem hasUniversalFlattening_iff :
    HasUniversalFlattening f ℱ ↔ IsAlgebraicSpace (overSFunctor f ℱ) :=
  sorry

/-- The algebraic space representing the `(Sch/S)` flattening functor, when that functor is
an algebraic space. -/
def space [IsAlgebraicSpace (overSFunctor f ℱ)] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (overSFunctor f ℱ)

/-- The functor of points of `space f ℱ` is `overSFunctor f ℱ`. -/
theorem space_functorOfPoints [IsAlgebraicSpace (overSFunctor f ℱ)] :
    (space f ℱ).functorOfPoints = overSFunctor f ℱ :=
  sorry

/-- The structural morphism from the universal flattening space to `Y`. -/
def toY [IsAlgebraicSpace (overSFunctor f ℱ)] : space f ℱ ⟶ Y :=
  overSFunctor_toY f ℱ

/-- `toY f ℱ` is the functor-of-points morphism `overSFunctor_toY f ℱ`. -/
theorem toY_eq [IsAlgebraicSpace (overSFunctor f ℱ)] :
    toY f ℱ = overSFunctor_toY f ℱ :=
  sorry

end Flattening

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The universal flattening of an algebraic space `X` over `Y` exists when the universal
flattening of `𝒪_X` exists. -/
abbrev HasUniversalFlattening : Prop :=
  Modules.Flattening.HasUniversalFlattening f
    (SheafOfModules.unit (structureSheaf X) : X.Modules)

/-- The universal flattening of `X` is the universal flattening of its structure module. -/
theorem hasUniversalFlattening_iff :
    HasUniversalFlattening f ↔
      Modules.Flattening.HasUniversalFlattening f
        (SheafOfModules.unit (structureSheaf X) : X.Modules) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
