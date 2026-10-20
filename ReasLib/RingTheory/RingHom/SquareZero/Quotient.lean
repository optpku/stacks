/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Quotient equivalence associated to a square-zero extension

For a square-zero surjection, quotienting the source by the annihilator of the kernel agrees with
quotienting the target by the descended annihilator.  The inverse map is constructed explicitly:
lift a target element to the source and then take its annihilator-quotient class.  Its public
specification makes the result independent of the selected lift.
-/

@[expose] public section

noncomputable section

universe u v

namespace RingHom.SquareZeroExtension

variable {R' : Type u} {R : Type v} [CommRing R'] [CommRing R]
variable (f : R' →+* R) [f.IsSquareZeroExtension]

/-- A selected source lift of a target element.  Public constructions use its specification, not
the selected representative itself. -/
def sourceLift (r : R) : R' :=
  Classical.choose (RingHom.IsSquareZeroExtension.surjective (f := f) r)

/-- The selected source lift maps to the target element. -/
@[simp]
theorem sourceLift_spec (r : R) :
    f (sourceLift f r) = r := sorry

/-- The quotient class of the selected lift of zero is zero. -/
theorem sourceLift_zero_mod :
    Ideal.Quotient.mk (sourceKernelAnnihilator f) (sourceLift f 0) = 0 := sorry

/-- The quotient class of the selected lift of one is one. -/
theorem sourceLift_one_mod :
    Ideal.Quotient.mk (sourceKernelAnnihilator f) (sourceLift f 1) = 1 := sorry

/-- Taking selected lifts and then annihilator-quotient classes preserves addition. -/
theorem sourceLift_add_mod (x y : R) :
    Ideal.Quotient.mk (sourceKernelAnnihilator f) (sourceLift f (x + y)) =
      Ideal.Quotient.mk (sourceKernelAnnihilator f) (sourceLift f x) +
        Ideal.Quotient.mk (sourceKernelAnnihilator f) (sourceLift f y) := sorry

/-- Taking selected lifts and then annihilator-quotient classes preserves multiplication. -/
theorem sourceLift_mul_mod (x y : R) :
    Ideal.Quotient.mk (sourceKernelAnnihilator f) (sourceLift f (x * y)) =
      Ideal.Quotient.mk (sourceKernelAnnihilator f) (sourceLift f x) *
        Ideal.Quotient.mk (sourceKernelAnnihilator f) (sourceLift f y) := sorry

/-- Send a target element to the source-annihilator quotient using any selected source lift. -/
def targetToSourceMap : R →+* sourceKernelQuotient f where
  toFun r := Ideal.Quotient.mk (sourceKernelAnnihilator f) (sourceLift f r)
  map_zero' := sourceLift_zero_mod f
  map_one' := sourceLift_one_mod f
  map_add' := sourceLift_add_mod f
  map_mul' := sourceLift_mul_mod f

/-- `targetToSourceMap` sends an element to the class of every source lift of that element. -/
theorem targetToSourceMap_eq_mk_of_map_eq (r : R) (x : R') (hx : f x = r) :
    targetToSourceMap f r =
      Ideal.Quotient.mk (sourceKernelAnnihilator f) x := sorry

/-- The descended kernel annihilator is killed by `targetToSourceMap`. -/
theorem targetToSourceMap_eq_zero_of_mem {r : R} (hr : r ∈ kernelAnnihilator f) :
    targetToSourceMap f r = 0 := sorry

/-- The inverse-direction map from the target annihilator quotient to the source annihilator
quotient. -/
@[stacks 09PS "inverse map between square-zero annihilator quotients"]
def targetQuotientMap :
    R ⧸ kernelAnnihilator f →+* sourceKernelQuotient f :=
  Ideal.Quotient.lift (kernelAnnihilator f) (targetToSourceMap f)
    (fun _ hr ↦ targetToSourceMap_eq_zero_of_mem f hr)

/-- The inverse-direction quotient map sends the class of `f x` to the class of `x`. -/
@[simp]
theorem targetQuotientMap_mk_map (x : R') :
    targetQuotientMap f
        (Ideal.Quotient.mk (kernelAnnihilator f) (f x)) =
      Ideal.Quotient.mk (sourceKernelAnnihilator f) x := sorry

/-- Mapping from the source quotient to the target quotient and back is the identity. -/
theorem targetQuotientMap_sourceQuotientMap (x : sourceKernelQuotient f) :
    targetQuotientMap f (sourceQuotientMap f x) = x := sorry

/-- Mapping from the target quotient to the source quotient and back is the identity. -/
theorem sourceQuotientMap_targetQuotientMap (x : R ⧸ kernelAnnihilator f) :
    sourceQuotientMap f (targetQuotientMap f x) = x := sorry

/-- The canonical ring equivalence between the source and target kernel-annihilator quotients. -/
@[stacks 09PS "equivalence of square-zero kernel-annihilator quotients"]
def sourceQuotientEquiv :
    sourceKernelQuotient f ≃+* R ⧸ kernelAnnihilator f where
  toFun := sourceQuotientMap f
  invFun := targetQuotientMap f
  left_inv := targetQuotientMap_sourceQuotientMap f
  right_inv := sourceQuotientMap_targetQuotientMap f
  map_mul' := map_mul (sourceQuotientMap f)
  map_add' := map_add (sourceQuotientMap f)

/-- The forward ring homomorphism of `sourceQuotientEquiv` is `sourceQuotientMap`. -/
@[simp]
theorem sourceQuotientEquiv_toRingHom :
    (sourceQuotientEquiv f).toRingHom = sourceQuotientMap f := sorry

/-- The inverse of `sourceQuotientEquiv` is `targetQuotientMap`. -/
@[simp]
theorem sourceQuotientEquiv_symm_apply (x : R ⧸ kernelAnnihilator f) :
    (sourceQuotientEquiv f).symm x = targetQuotientMap f x := sorry

end RingHom.SquareZeroExtension
