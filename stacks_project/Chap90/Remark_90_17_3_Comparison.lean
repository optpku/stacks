/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Logic.Equiv.Basic
public import stacks_project.Chap90.Definition_90_17_1_ObjectLift
public import stacks_project.Chap90.Remark_90_6_4
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap90.«90_17_5_3_SquareZero»

/-!
# Identification of residue-fibre lifts along `k[V]` with the slice fibre

For a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k`, a residue-fibre
object `x0`, and a finite-dimensional `k`-vector space `V`, lifts of `x0` along
`squareZeroToResidue Λ k V` are the objects of the slice fibre
`(Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).Fiber (squareZero Λ k V)`,
and isomorphism classes of lifts identify with the value of the slice
isomorphism-class functor at `k[V]`.
-/

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
variable (x0 : p.Fiber (residue Λ k))

/-- The residue slice of Remark 90.6.4 is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_overForget :
    IsFibered.InGroupoids (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

variable (V : FGModuleCat.{u} k)

/-- The underlying over-object of a lift of `x0` along `k[V] ⟶ k` lies in the slice
fibre over `k[V]`. -/
theorem objectLift_obj_squareZero
    (a : ObjectLift p (squareZeroToResidue Λ k V) x0) :
    (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).obj a.val =
      squareZero Λ k V := sorry

/-- An object of the slice fibre over `k[V]` is a morphism to `x0` lying over
`squareZeroToResidue Λ k V`. -/
theorem isHomLift_squareZero_of_overFiber
    (y : (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).Fiber (squareZero Λ k V)) :
    p.IsHomLift (squareZeroToResidue Λ k V) y.val.hom := sorry

/-- Objects of `ObjectLift p (squareZeroToResidue Λ k V) x0` correspond to objects of
the slice fibre over `k[V]`. -/
noncomputable def objectLiftSquareZeroEquivFiber :
    ObjectLift p (squareZeroToResidue Λ k V) x0 ≃
      (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).Fiber (squareZero Λ k V) where
  toFun a := ⟨a.val, objectLift_obj_squareZero p x0 V a⟩
  invFun y := ⟨y.val, isHomLift_squareZero_of_overFiber p x0 V y⟩
  left_inv := sorry
  right_inv := sorry

/-- `objectLiftSquareZeroEquivFiber` sends a lift to its underlying over-object, viewed
in the slice fibre. -/
theorem objectLiftSquareZeroEquivFiber_apply
    (a : ObjectLift p (squareZeroToResidue Λ k V) x0) :
    objectLiftSquareZeroEquivFiber p x0 V a =
      ⟨a.val, objectLift_obj_squareZero p x0 V a⟩ := sorry

/-- The inverse of `objectLiftSquareZeroEquivFiber` recovers the packaged lift of the
underlying over-morphism. -/
theorem objectLiftSquareZeroEquivFiber_symm_apply
    (y : (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).Fiber (squareZero Λ k V)) :
    (objectLiftSquareZeroEquivFiber p x0 V).symm y =
      ⟨y.val, isHomLift_squareZero_of_overFiber p x0 V y⟩ := sorry

/-- Isomorphism classes of lifts of `x0` along `k[V] ⟶ k` are the isomorphism classes
of the slice fibre `F_x0(k[V])`. -/
noncomputable def liftsSquareZeroEquivIsoClass :
    lifts p (squareZeroToResidue Λ k V) x0 ≃
      (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
        (squareZero Λ k V) where
  toFun :=
    Quotient.map (objectLiftSquareZeroEquivFiber p x0 V) fun _ _ _ ↦ sorry
  invFun :=
    Quotient.map (objectLiftSquareZeroEquivFiber p x0 V).symm fun _ _ _ ↦ sorry
  left_inv := sorry
  right_inv := sorry

/-- On a represented class, `liftsSquareZeroEquivIsoClass` is
`objectLiftSquareZeroEquivFiber` of the representative. -/
theorem liftsSquareZeroEquivIsoClass_mk
    (a : ObjectLift p (squareZeroToResidue Λ k V) x0) :
    liftsSquareZeroEquivIsoClass p x0 V (Quotient.mk'' a) =
      Quotient.mk'' (objectLiftSquareZeroEquivFiber p x0 V a) := sorry

end CategoryTheory.Functor
