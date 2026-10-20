/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.Dimension.Free
public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroFunctor
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Localization
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Types
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor

/-!
# Square-zero lifts and tangent tensors

Lifts of a residue-fibre object along a square-zero extension identify with the
isomorphism classes of its residue slice. Under Schlessinger's second condition,
finite-basis coordinates identify these classes with the tangent tensor product.
-/

@[expose] public section

noncomputable section

set_option backward.privateInPublic true

open CategoryTheory
open ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
variable (x0 : p.Fiber (residue Λ k)) (V : FGModuleCat.{u} k)

/-- The underlying over-object of a square-zero lift lies over the square-zero algebra. -/
theorem objectLift_obj_squareZero
    (a : ObjectLift p (squareZeroToResidue Λ k V) x0) :
    (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).obj a.val =
      squareZero Λ k V := sorry

/-- A square-zero residue-slice fibre object lies over the augmentation to the residue field. -/
theorem isHomLift_squareZero_of_overFiber
    (y : (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).Fiber (squareZero Λ k V)) :
    p.IsHomLift (squareZeroToResidue Λ k V) y.val.hom := sorry

/-- Repackaging a lift in the residue-slice fibre and back recovers the lift. -/
private theorem objectLiftSquareZeroEquivFiber_left_inv :
    Function.LeftInverse
      (fun y : (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).Fiber
          (squareZero Λ k V) ↦
        (⟨y.val, isHomLift_squareZero_of_overFiber p x0 V y⟩ :
          ObjectLift p (squareZeroToResidue Λ k V) x0))
      (fun a : ObjectLift p (squareZeroToResidue Λ k V) x0 ↦
        ⟨a.val, objectLift_obj_squareZero p x0 V a⟩) := sorry

/-- Repackaging a residue-slice fibre object as a lift and back recovers the object. -/
private theorem objectLiftSquareZeroEquivFiber_right_inv :
    Function.RightInverse
      (fun y : (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).Fiber
          (squareZero Λ k V) ↦
        (⟨y.val, isHomLift_squareZero_of_overFiber p x0 V y⟩ :
          ObjectLift p (squareZeroToResidue Λ k V) x0))
      (fun a : ObjectLift p (squareZeroToResidue Λ k V) x0 ↦
        ⟨a.val, objectLift_obj_squareZero p x0 V a⟩) := sorry

/-- Square-zero lifts correspond to objects of the square-zero fibre of the residue slice. -/
def objectLiftSquareZeroEquivFiber :
    ObjectLift p (squareZeroToResidue Λ k V) x0 ≃
      (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).Fiber (squareZero Λ k V) where
  toFun a := ⟨a.val, objectLift_obj_squareZero p x0 V a⟩
  invFun y := ⟨y.val, isHomLift_squareZero_of_overFiber p x0 V y⟩
  left_inv := objectLiftSquareZeroEquivFiber_left_inv p x0 V
  right_inv := objectLiftSquareZeroEquivFiber_right_inv p x0 V

/-- The object comparison preserves the underlying over-object of a lift. -/
theorem objectLiftSquareZeroEquivFiber_apply
    (a : ObjectLift p (squareZeroToResidue Λ k V) x0) :
    objectLiftSquareZeroEquivFiber p x0 V a =
      ⟨a.val, objectLift_obj_squareZero p x0 V a⟩ := sorry

/-- The inverse object comparison preserves the underlying over-object of a fibre object. -/
theorem objectLiftSquareZeroEquivFiber_symm_apply
    (y : (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).Fiber (squareZero Λ k V)) :
    (objectLiftSquareZeroEquivFiber p x0 V).symm y =
      ⟨y.val, isHomLift_squareZero_of_overFiber p x0 V y⟩ := sorry

/-- Isomorphic lifts give isomorphic objects in the residue-slice fibre. -/
theorem objectLiftSquareZeroEquivFiber_preserves_iso
    (a b : ObjectLift p (squareZeroToResidue Λ k V) x0) (h : IsIsomorphic a b) :
    IsIsomorphic (objectLiftSquareZeroEquivFiber p x0 V a)
      (objectLiftSquareZeroEquivFiber p x0 V b) := sorry

/-- Isomorphic residue-slice fibre objects give isomorphic lifts. -/
theorem objectLiftSquareZeroEquivFiber_symm_preserves_iso
    (y z : (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p).Fiber (squareZero Λ k V))
    (h : IsIsomorphic y z) :
    IsIsomorphic ((objectLiftSquareZeroEquivFiber p x0 V).symm y)
      ((objectLiftSquareZeroEquivFiber p x0 V).symm z) := sorry

/-- The quotient comparison followed by its inverse recovers each lift class. -/
private theorem liftsSquareZeroEquivIsoClass_left_inv :
    Function.LeftInverse
      (Quotient.map (objectLiftSquareZeroEquivFiber p x0 V).symm
        (fun {left right} isomorphism ↦
          objectLiftSquareZeroEquivFiber_symm_preserves_iso p x0 V left right isomorphism) :
        (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
          (squareZero Λ k V) → lifts p (squareZeroToResidue Λ k V) x0)
      (Quotient.map (objectLiftSquareZeroEquivFiber p x0 V)
        (fun {left right} isomorphism ↦
          objectLiftSquareZeroEquivFiber_preserves_iso p x0 V left right isomorphism)) := sorry

/-- The inverse quotient comparison followed by the comparison recovers each fibre class. -/
private theorem liftsSquareZeroEquivIsoClass_right_inv :
    Function.RightInverse
      (Quotient.map (objectLiftSquareZeroEquivFiber p x0 V).symm
        (fun {left right} isomorphism ↦
          objectLiftSquareZeroEquivFiber_symm_preserves_iso p x0 V left right isomorphism) :
        (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
          (squareZero Λ k V) → lifts p (squareZeroToResidue Λ k V) x0)
      (Quotient.map (objectLiftSquareZeroEquivFiber p x0 V)
        (fun {left right} isomorphism ↦
          objectLiftSquareZeroEquivFiber_preserves_iso p x0 V left right isomorphism)) := sorry

/-- Square-zero lift classes are the isomorphism classes of the residue-slice fibre. -/
def liftsSquareZeroEquivIsoClass :
    lifts p (squareZeroToResidue Λ k V) x0 ≃
      (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
        (squareZero Λ k V) where
  toFun := Quotient.map (objectLiftSquareZeroEquivFiber p x0 V)
    (fun {left right} isomorphism ↦
      objectLiftSquareZeroEquivFiber_preserves_iso p x0 V left right isomorphism)
  invFun := Quotient.map (objectLiftSquareZeroEquivFiber p x0 V).symm
    (fun {left right} isomorphism ↦
      objectLiftSquareZeroEquivFiber_symm_preserves_iso p x0 V left right isomorphism)
  left_inv := liftsSquareZeroEquivIsoClass_left_inv p x0 V
  right_inv := liftsSquareZeroEquivIsoClass_right_inv p x0 V

/-- The quotient comparison sends a represented lift to its corresponding fibre class. -/
theorem liftsSquareZeroEquivIsoClass_mk
    (a : ObjectLift p (squareZeroToResidue Λ k V) x0) :
    liftsSquareZeroEquivIsoClass p x0 V (Quotient.mk'' a) =
      Quotient.mk'' (objectLiftSquareZeroEquivFiber p x0 V a) := sorry

variable [HasSchlessingerS2 p]

/-- The isomorphism-class functor of a residue slice satisfies the second Schlessinger
condition when the original category does. -/
instance instHasSchlessingerH2_fiberIsoClass_overForget :
    HasSchlessingerH2
      (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)) := sorry

/-- Square-zero lift classes inherit addition from the residue-slice isomorphism classes. -/
instance instAddCommGroup_liftsSquareZero :
    AddCommGroup (lifts p (squareZeroToResidue Λ k V) x0) :=
  Equiv.addCommGroup (liftsSquareZeroEquivIsoClass p x0 V)

/-- Square-zero lift classes inherit scalar multiplication from the residue slice. -/
instance instModule_liftsSquareZero :
    Module k (lifts p (squareZeroToResidue Λ k V) x0) :=
  Equiv.module k (liftsSquareZeroEquivIsoClass p x0 V)

/-- Expand a square-zero lift class as a sum of its tangent coordinates tensored with
the corresponding finite-basis vectors. -/
private def liftsSquareZeroTensorCoordinatesFun
    (value : lifts p (squareZeroToResidue Λ k V) x0) :
    (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
        (dualNumber Λ k) ⊗[k] V :=
  let basis := Module.finBasis k V
  let slice := Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p
  let fibreClass := liftsSquareZeroEquivIsoClass p x0 V value
  ∑ index, (fiberIsoClassFunctor slice).map
    (squareZeroMap (basis.coord index) ≫ (dualNumberIsoSquareZero Λ k).inv)
      fibreClass ⊗ₜ[k] basis index

/-- Tangent-coordinate expansion preserves addition of lift classes. -/
private theorem liftsSquareZeroTensorCoordinates_add
    (left right : lifts p (squareZeroToResidue Λ k V) x0) :
    liftsSquareZeroTensorCoordinatesFun p x0 V (left + right) =
      liftsSquareZeroTensorCoordinatesFun p x0 V left +
        liftsSquareZeroTensorCoordinatesFun p x0 V right := sorry

/-- Tangent-coordinate expansion preserves scalar multiplication of lift classes. -/
private theorem liftsSquareZeroTensorCoordinates_smul
    (scalar : k) (value : lifts p (squareZeroToResidue Λ k V) x0) :
    liftsSquareZeroTensorCoordinatesFun p x0 V (scalar • value) =
      scalar • liftsSquareZeroTensorCoordinatesFun p x0 V value := sorry

/-- The linear tangent-coordinate expansion of square-zero lift classes. -/
def liftsSquareZeroTensorCoordinates :
    lifts p (squareZeroToResidue Λ k V) x0 →ₗ[k]
      (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
          (dualNumber Λ k) ⊗[k] V where
  toFun := liftsSquareZeroTensorCoordinatesFun p x0 V
  map_add' := liftsSquareZeroTensorCoordinates_add p x0 V
  map_smul' := liftsSquareZeroTensorCoordinates_smul p x0 V

/-- The canonical tangent-tensor comparison, transported to square-zero lift classes. -/
def liftsSquareZeroTensorMap :
    (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
        (dualNumber Λ k) ⊗[k] V →ₗ[k]
      lifts p (squareZeroToResidue Λ k V) x0 :=
  (Equiv.linearEquiv k (liftsSquareZeroEquivIsoClass p x0 V)).symm.toLinearMap.comp
    (fiberDualTangentTensor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p) V)

/-- Applying the tensor comparison after tangent-coordinate expansion recovers a lift class. -/
private theorem liftsSquareZeroTensorCoordinates_left_inv :
    Function.LeftInverse (liftsSquareZeroTensorMap p x0 V)
      (liftsSquareZeroTensorCoordinates p x0 V) := sorry

/-- Tangent-coordinate expansion after the tensor comparison recovers a tangent tensor. -/
private theorem liftsSquareZeroTensorCoordinates_right_inv :
    Function.RightInverse (liftsSquareZeroTensorMap p x0 V)
      (liftsSquareZeroTensorCoordinates p x0 V) := sorry

/-- Square-zero lift classes are linearly equivalent to the residue-slice tangent space
tensored with the finite-dimensional square-zero module. -/
def liftsSquareZeroLinearEquiv :
    lifts p (squareZeroToResidue Λ k V) x0 ≃ₗ[k]
      (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
          (dualNumber Λ k) ⊗[k] V :=
  { liftsSquareZeroTensorCoordinates p x0 V with
    invFun := liftsSquareZeroTensorMap p x0 V
    left_inv := liftsSquareZeroTensorCoordinates_left_inv p x0 V
    right_inv := liftsSquareZeroTensorCoordinates_right_inv p x0 V }

/-- The inverse tangent-space equivalence is the canonical tensor-to-lift linear map. -/
theorem liftsSquareZeroLinearEquiv_spec :
    (liftsSquareZeroLinearEquiv p x0 V).symm.toLinearMap =
      liftsSquareZeroTensorMap p x0 V := sorry

end CategoryTheory.Functor
