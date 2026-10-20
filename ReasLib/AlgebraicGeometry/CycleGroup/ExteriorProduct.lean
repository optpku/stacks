/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.CycleGroup.Total
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

/-!
# Exterior products of cycles over a field

This file constructs the degreewise exterior product of cycles from product-point cycles and
assembles it into an exterior product on total relative cycle homology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

namespace SchemeOverField

/-- The ideal cutting out the product of the reduced closures of two points in the
fibre product over a field. -/
noncomputable def pointProductIdeal (X Y : SchemeOverField k)
    (x : X.left) (y : Y.left) : (X ⨯ Y).left.IdealSheafData :=
  ((Scheme.PointClosure.reducedStructure x).ideal.comap
      ((Limits.prod.fst : X ⨯ Y ⟶ X)).left) ⊔
    ((Scheme.PointClosure.reducedStructure y).ideal.comap
      ((Limits.prod.snd : X ⨯ Y ⟶ Y)).left)

/-- The product-point ideal is the sum of the pullbacks of the two reduced
point-closure ideals. -/
theorem pointProductIdeal_def (X Y : SchemeOverField k)
    (x : X.left) (y : Y.left) :
    pointProductIdeal X Y x y =
      ((Scheme.PointClosure.reducedStructure x).ideal.comap
          ((Limits.prod.fst : X ⨯ Y ⟶ X)).left) ⊔
        ((Scheme.PointClosure.reducedStructure y).ideal.comap
          ((Limits.prod.snd : X ⨯ Y ⟶ Y)).left) := sorry

end SchemeOverField

namespace CycleGroup

/-- The degree-`n + m` cycle associated to the product of the reduced closures of
degree-`n` and degree-`m` points. -/
noncomputable def pointProductCycle (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (x : X.left) (y : Y.left)
    (hx : X.hom.relativeDimensionFunction (fun _ ↦ 0) x = n)
    (hy : Y.hom.relativeDimensionFunction (fun _ ↦ 0) y = m) :
    CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m) :=
  @Scheme.IdealSheafData.associatedCycle (X ⨯ Y).left
    (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance
      (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
        (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
    (SchemeOverField.pointProductIdeal X Y x y)
    ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m)

/-- The product-point cycle is the associated cycle of the product-point ideal. -/
theorem pointProductCycle_def (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (x : X.left) (y : Y.left)
    (hx : X.hom.relativeDimensionFunction (fun _ ↦ 0) x = n)
    (hy : Y.hom.relativeDimensionFunction (fun _ ↦ 0) y = m) :
    pointProductCycle X Y n m x y hx hy =
      @Scheme.IdealSheafData.associatedCycle (X ⨯ Y).left
        (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        (SchemeOverField.pointProductIdeal X Y x y)
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m) := sorry

/-- The contribution of a pair of points to the exterior product of two cycles. -/
noncomputable def exteriorProductTerm (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m)
    (x : X.left) (y : Y.left) :
    CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m) :=
  if hx : X.hom.relativeDimensionFunction (fun _ ↦ 0) x = n then
    if hy : Y.hom.relativeDimensionFunction (fun _ ↦ 0) y = m then
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n alpha x *
          toAlgebraicCycle (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m beta y) •
        pointProductCycle X Y n m x y hx hy
    else 0
  else 0

/-- The point-pair terms in the exterior-product formula have locally finite support. -/
theorem exteriorProductTermsLocallyFinite (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) :
    LocallyFinite fun p : X.left × Y.left ↦
      (toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m)
        (exteriorProductTerm X Y n m alpha beta p.1 p.2)).support := sorry

/-- The concrete exterior product of two cycles, formed as the locally finite sum over
pairs of points. -/
noncomputable def exteriorProductValue (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) :
    CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m) :=
  locallyFiniteSum ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m)
    (fun p : X.left × Y.left ↦ exteriorProductTerm X Y n m alpha beta p.1 p.2)
    (exteriorProductTermsLocallyFinite X Y n m alpha beta)

/-- The concrete exterior product vanishes when its right input is zero. -/
theorem exteriorProductValue_zero_right (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    exteriorProductValue X Y n m alpha 0 = 0 := sorry

/-- The concrete exterior product is additive in its right input. -/
theorem exteriorProductValue_add_right (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta gamma : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) :
    exteriorProductValue X Y n m alpha (beta + gamma) =
      exteriorProductValue X Y n m alpha beta +
        exteriorProductValue X Y n m alpha gamma := sorry

/-- Exterior product by a fixed cycle in the left variable is an additive homomorphism. -/
noncomputable def exteriorProductRight (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m →+
      CycleGroup (X ⨯ Y).left
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m) where
  toFun := exteriorProductValue X Y n m alpha
  map_zero' := exteriorProductValue_zero_right X Y n m alpha
  map_add' := exteriorProductValue_add_right X Y n m alpha

/-- The right-variable exterior-product homomorphism evaluates to the concrete double sum. -/
theorem exteriorProductRight_apply (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) :
    exteriorProductRight X Y n m alpha beta =
      exteriorProductValue X Y n m alpha beta := sorry

/-- The right-variable exterior-product homomorphism vanishes at a zero left input. -/
theorem exteriorProductRight_zero (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    exteriorProductRight X Y n m 0 = 0 := sorry

/-- The right-variable exterior-product homomorphism is additive in its left input. -/
theorem exteriorProductRight_add (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha beta : CycleGroup X.left
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    exteriorProductRight X Y n m (alpha + beta) =
      exteriorProductRight X Y n m alpha + exteriorProductRight X Y n m beta := sorry

/-- The cycle-level exterior product as a biadditive pairing. -/
noncomputable def exteriorProductPairing (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n →+
      CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m →+
        CycleGroup (X ⨯ Y).left
          ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m) where
  toFun := exteriorProductRight X Y n m
  map_zero' := exteriorProductRight_zero X Y n m
  map_add' := exteriorProductRight_add X Y n m

/-- Coefficients of the cycle-level exterior product are the locally finite double sum of
the input coefficients times the product-point cycles. -/
theorem exteriorProductPairing_apply (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m)
    (z : (X ⨯ Y).left) :
    toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m)
        (exteriorProductPairing X Y n m alpha beta) z =
      ∑ᶠ p : X.left × Y.left,
        toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m)
          (exteriorProductTerm X Y n m alpha beta p.1 p.2) z := sorry

/-- The cycle pairing is balanced over `ℤ`. -/
theorem exteriorProductPairing_zsmul (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (r : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) :
    exteriorProductPairing X Y n m (r • alpha) beta =
      exteriorProductPairing X Y n m alpha (r • beta) := sorry

/-- The cycle-level exterior product induced on the tensor product over `ℤ`. -/
noncomputable def exteriorProduct (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    TensorProduct ℤ
        (CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
        (CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) →+
      CycleGroup (X ⨯ Y).left
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m) :=
  TensorProduct.liftAddHom (exteriorProductPairing X Y n m)
    (exteriorProductPairing_zsmul X Y n m)

/-- The tensor-level cycle exterior product evaluates on a pure tensor by the cycle pairing. -/
theorem exteriorProduct_tmul (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) :
    exteriorProduct X Y n m (alpha ⊗ₜ[ℤ] beta) =
      exteriorProductPairing X Y n m alpha beta := sorry

namespace Total

/-- The exterior product on total relative cycles over a field, assembled from the
degreewise exterior-product pairings. -/
noncomputable def exteriorProduct (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) Y →+
      Total (fun _ ↦ 0) (X ⨯ Y) :=
  DirectSum.toAddMonoid fun n ↦
    AddMonoidHom.flip <| DirectSum.toAddMonoid fun m ↦
      AddMonoidHom.flip <|
        (DirectSum.of (fun d : ℤ ↦ CycleGroup (X ⨯ Y).left
          ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) d) (n + m)).compHom.comp
            (CycleGroup.exteriorProductPairing X Y n m)

/-- The total cycle exterior product of homogeneous cycles is the homogeneous degreewise
exterior product in degree `n + m`. -/
theorem exteriorProduct_of (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) :
    exteriorProduct X Y
        (DirectSum.of (fun d : ℤ ↦ CycleGroup X.left
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) d) n alpha)
        (DirectSum.of (fun d : ℤ ↦ CycleGroup Y.left
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) d) m beta) =
      DirectSum.of (fun d : ℤ ↦ CycleGroup (X ⨯ Y).left
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) d) (n + m)
          (CycleGroup.exteriorProductPairing X Y n m alpha beta) := sorry

/-- The exterior product on total cycles is associative after pushforward along the canonical
associator from `(X ⨯ Y) ⨯ Z` to `X ⨯ (Y ⨯ Z)`. -/
theorem exteriorProduct_assoc {X Y Z : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom]
    (alpha : Total (fun _ ↦ 0) X) (beta : Total (fun _ ↦ 0) Y)
    (gamma : Total (fun _ ↦ 0) Z) :
    map (fun _ ↦ 0) (Limits.prod.associator X Y Z).hom
        (exteriorProduct (X ⨯ Y) Z (exteriorProduct X Y alpha beta) gamma) =
      exteriorProduct X (Y ⨯ Z) alpha (exteriorProduct Y Z beta gamma) := sorry

end Total

end CycleGroup

end AlgebraicGeometry
