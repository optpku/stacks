/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Shift
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Endomorphism.Right
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left.Shift
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded actions on shifted internal Hom

A left action on the source of a Hom complex induces a right action of the same algebra on the
internal Hom, while a right action induces a left action.  This file owns both constructions and
the first-variable shift isomorphism, with both handedness cases expressed through the canonical
right- and signed left-DG-module shifts.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open CochainComplex.HomComplex

namespace DifferentialGradedModule.InternalHom

variable {R : Type u} [CommRing R]

namespace OfLeft

/-- The degree-`i` action cochain induced by a fixed-underlying left differential graded module. -/
abbrev actionCochain
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (i : ℤ) (a : A.X i) : Cochain M M i :=
  Cochain.mk fun p _ hpq ↦
    ModuleCat.ofHom <|
      ModuleCat.castLinearMap (congrArg M.X ((add_comm i p).trans hpq))
        (rho.toEndomorphismDGAHom.map i a p)

/-- The left action cochain on `M⟦k⟧`, including the canonical Koszul sign
`(-1)^(i * k)` for an algebra element of degree `i`. -/
abbrev shiftedActionCochain
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k i : ℤ) (a : A.X i) : Cochain (M⟦k⟧) (M⟦k⟧) i :=
  ((i * k).negOnePow : R) • (actionCochain rho i a).shift k

/-- The shifted left action cochain is the simultaneous shift twisted by its Koszul sign. -/
@[simp]
theorem shiftedActionCochain_eq
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k i : ℤ) (a : A.X i) :
    shiftedActionCochain rho k i a =
      ((i * k).negOnePow : R) • (actionCochain rho i a).shift k := sorry

/-- A left action on `M` induces the opposite-handed endomorphism action on `Hom^•(M, N)`. -/
def rightEndomorphismDGAHom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M)) :
    EndomorphismDGAHom A.opposite (moduleFamily R M N) (moduleDifferential R M N) where
  map i :=
    { toFun := fun a p ↦
        { toFun := fun f ↦ (actionCochain rho i a).comp f rfl
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  d_sq := sorry
  map_one := sorry
  map_mul := sorry
  comm_d := sorry

/-- The right differential graded module structure induced on `Hom^•(M, N)`. -/
def rightWithFixedUnderlying
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M)) :
    DifferentialGradedModule.WithFixedUnderlying A
      (moduleFamily R M N) (moduleDifferential R M N) :=
  DifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (rightEndomorphismDGAHom N rho)

/-- Shifting the source gives the induced right endomorphism action on `Hom^•(M⟦k⟧, N)`. -/
def shiftedSourceRightEndomorphismDGAHom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) :
    EndomorphismDGAHom A.opposite
      (moduleFamily R (M⟦k⟧) N) (moduleDifferential R (M⟦k⟧) N) where
  map i :=
    { toFun := fun a p ↦
        { toFun := fun f ↦ (shiftedActionCochain rho k i a).comp f rfl
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  d_sq := sorry
  map_one := sorry
  map_mul := sorry
  comm_d := sorry

/-- The induced right differential graded module structure on `Hom^•(M⟦k⟧, N)`. -/
def shiftedSourceRightWithFixedUnderlying
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) :
    DifferentialGradedModule.WithFixedUnderlying A
      (moduleFamily R (M⟦k⟧) N) (moduleDifferential R (M⟦k⟧) N) :=
  DifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (shiftedSourceRightEndomorphismDGAHom N rho k)

/-- The bundled right differential graded module on `Hom^•(M, N)`. -/
abbrev right
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M)) : DifferentialGradedModule A :=
  (rightWithFixedUnderlying N rho).toRightDifferentialGradedModule

/-- The canonical right-DG-module shift on `Hom^•(M, N)[-k]`. -/
abbrev shiftedRight
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) : DifferentialGradedModule A :=
  DifferentialGradedModule.shift (right N rho) (-k)

/-- The bundled right differential graded module on `Hom^•(M⟦k⟧, N)`. -/
abbrev shiftedSourceRight
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) : DifferentialGradedModule A :=
  (shiftedSourceRightWithFixedUnderlying N rho k).toRightDifferentialGradedModule

/-- The forward first-variable shift map for internal Hom from a left DG action. -/
def leftShiftHom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) : shiftedRight N rho k ⟶ shiftedSourceRight N rho k where
  hom n :=
    (Cochain.leftShiftLinearEquiv R M N (n - k) k n (sub_add_cancel n k)).toLinearMap
  comm_d := sorry
  comm_smul := sorry

/-- The degree-`n` component of the first-variable shift map from a left action is the canonical
linear shift equivalence. -/
@[simp]
theorem leftShiftHom_hom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k n : ℤ) :
    (leftShiftHom N rho k).hom n =
      (Cochain.leftShiftLinearEquiv R M N (n - k) k n
        (sub_add_cancel n k)).toLinearMap := sorry

/-- The inverse first-variable shift map for internal Hom from a left DG action. -/
def leftShiftInv
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) : shiftedSourceRight N rho k ⟶ shiftedRight N rho k where
  hom n :=
    (Cochain.leftShiftLinearEquiv R M N (n - k) k n (sub_add_cancel n k)).symm.toLinearMap
  comm_d := sorry
  comm_smul := sorry

/-- The degree-`n` component of the inverse first-variable shift map from a left action is the
inverse linear shift equivalence. -/
@[simp]
theorem leftShiftInv_hom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k n : ℤ) :
    (leftShiftInv N rho k).hom n =
      (Cochain.leftShiftLinearEquiv R M N (n - k) k n
        (sub_add_cancel n k)).symm.toLinearMap := sorry

/-- The fixed-underlying first-variable shift isomorphism induced by a left DG action. -/
def leftShiftIso
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) : shiftedRight N rho k ≅ shiftedSourceRight N rho k where
  hom := leftShiftHom N rho k
  inv := leftShiftInv N rho k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the first-variable shift isomorphism from a left action is
`leftShiftHom`. -/
@[simp]
theorem leftShiftIso_hom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M)) (k : ℤ) :
    (leftShiftIso N rho k).hom = leftShiftHom N rho k := sorry

/-- The inverse map of the first-variable shift isomorphism from a left action is
`leftShiftInv`. -/
@[simp]
theorem leftShiftIso_inv
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M)) (k : ℤ) :
    (leftShiftIso N rho k).inv = leftShiftInv N rho k := sorry

namespace Action

/-- The right DG module on `Hom^•(M, N)` induced by a genuine left action on `M`. -/
abbrev right
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.ActionOn A M) :
    DifferentialGradedModule A :=
  OfLeft.right N rho.toFixed

/-- The canonical right-DG-module shift of the internal Hom induced by a genuine left action. -/
abbrev shiftedRight
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.ActionOn A M) (k : ℤ) :
    DifferentialGradedModule A :=
  OfLeft.shiftedRight N rho.toFixed k

/-- The right DG module on `Hom^•(M⟦k⟧, N)` induced by the shifted genuine left action. -/
abbrev shiftedSourceRight
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.ActionOn A M) (k : ℤ) :
    DifferentialGradedModule A :=
  OfLeft.shiftedSourceRight N rho.toFixed k

/-- The forward first-variable shift map induced by a genuine left DG action. -/
abbrev shiftHom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.ActionOn A M) (k : ℤ) :
    shiftedRight N rho k ⟶ shiftedSourceRight N rho k :=
  OfLeft.leftShiftHom N rho.toFixed k

/-- The inverse first-variable shift map induced by a genuine left DG action. -/
abbrev shiftInv
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.ActionOn A M) (k : ℤ) :
    shiftedSourceRight N rho k ⟶ shiftedRight N rho k :=
  OfLeft.leftShiftInv N rho.toFixed k

/-- Remark 22.13.7 (0FQ9) (2): first-variable shift is an isomorphism of right differential
graded modules when the source carries a genuine left DG action. -/
@[stacks 0FQ9 "first-variable shift isomorphism from a left DG action"]
def shiftIso
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.ActionOn A M) (k : ℤ) :
    shiftedRight N rho k ≅ shiftedSourceRight N rho k :=
  OfLeft.leftShiftIso N rho.toFixed k

/-- The forward map of `shiftIso` is `shiftHom`. -/
@[simp]
theorem shiftIso_hom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.ActionOn A M) (k : ℤ) :
    (shiftIso N rho k).hom = shiftHom N rho k := sorry

/-- The inverse map of `shiftIso` is `shiftInv`. -/
@[simp]
theorem shiftIso_inv
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : LeftDifferentialGradedModule.ActionOn A M) (k : ℤ) :
    (shiftIso N rho k).inv = shiftInv N rho k := sorry

end Action

end OfLeft

namespace OfRight

/-- The degree-`i` action cochain induced by a fixed-underlying right differential graded module. -/
abbrev actionCochain
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (i : ℤ) (a : A.X i) : Cochain M M i :=
  Cochain.mk fun p _ hpq ↦
    ModuleCat.ofHom <|
      ModuleCat.castLinearMap (congrArg M.X ((add_comm i p).trans hpq))
        (rho.toEndomorphismDGAHom.map i a p)

/-- The right action cochain on a simultaneous shift of the source complex. -/
abbrev shiftedActionCochain
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k i : ℤ) (a : A.X i) : Cochain (M⟦k⟧) (M⟦k⟧) i :=
  (actionCochain rho i a).shift k

/-- The shifted right action cochain is the simultaneous shift without an additional action
sign. -/
@[simp]
theorem shiftedActionCochain_eq
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k i : ℤ) (a : A.X i) :
    shiftedActionCochain rho k i a = (actionCochain rho i a).shift k := sorry

/-- A right action on `M` induces the left endomorphism action on `Hom^•(M, N)`. -/
def leftEndomorphismDGAHom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M)) :
    EndomorphismDGAHom A (moduleFamily R M N) (moduleDifferential R M N) where
  map i :=
    { toFun := fun a p ↦
        { toFun := fun f ↦ (actionCochain rho i a).comp f rfl
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  d_sq := sorry
  map_one := sorry
  map_mul := sorry
  comm_d := sorry

/-- The left differential graded module structure induced on `Hom^•(M, N)`. -/
def leftWithFixedUnderlying
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M)) :
    LeftDifferentialGradedModule.WithFixedUnderlying A
      (moduleFamily R M N) (moduleDifferential R M N) :=
  LeftDifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (leftEndomorphismDGAHom N rho)

/-- Shifting the source gives the induced left endomorphism action on `Hom^•(M⟦k⟧, N)`. -/
def shiftedSourceLeftEndomorphismDGAHom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) :
    EndomorphismDGAHom A
      (moduleFamily R (M⟦k⟧) N) (moduleDifferential R (M⟦k⟧) N) where
  map i :=
    { toFun := fun a p ↦
        { toFun := fun f ↦ (shiftedActionCochain rho k i a).comp f rfl
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  d_sq := sorry
  map_one := sorry
  map_mul := sorry
  comm_d := sorry

/-- The induced left differential graded module structure on `Hom^•(M⟦k⟧, N)`. -/
def shiftedSourceLeftWithFixedUnderlying
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) :
    LeftDifferentialGradedModule.WithFixedUnderlying A
      (moduleFamily R (M⟦k⟧) N) (moduleDifferential R (M⟦k⟧) N) :=
  LeftDifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (shiftedSourceLeftEndomorphismDGAHom N rho k)

/-- The bundled left differential graded module on `Hom^•(M, N)`. -/
abbrev left
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M)) : LeftDifferentialGradedModule A :=
  (leftWithFixedUnderlying N rho).toLeftDifferentialGradedModule

/-- The canonical signed left-DG-module shift on `Hom^•(M, N)[-k]`. -/
abbrev shiftedLeft
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) : LeftDifferentialGradedModule A :=
  LeftDifferentialGradedModule.shift (left N rho) (-k)

/-- The bundled left differential graded module on `Hom^•(M⟦k⟧, N)`. -/
abbrev shiftedSourceLeft
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) : LeftDifferentialGradedModule A :=
  (shiftedSourceLeftWithFixedUnderlying N rho k).toLeftDifferentialGradedModule

/-- The forward first-variable shift map for internal Hom from a right DG action. -/
def leftShiftHom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) : shiftedLeft N rho k ⟶ shiftedSourceLeft N rho k where
  hom n :=
    (Cochain.leftShiftLinearEquiv R M N (n - k) k n (sub_add_cancel n k)).toLinearMap
  comm_d := sorry
  comm_smul := sorry

/-- The degree-`n` component of the first-variable shift map from a right action is the canonical
linear shift equivalence. -/
@[simp]
theorem leftShiftHom_hom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k n : ℤ) :
    (leftShiftHom N rho k).hom n =
      (Cochain.leftShiftLinearEquiv R M N (n - k) k n
        (sub_add_cancel n k)).toLinearMap := sorry

/-- The inverse first-variable shift map for internal Hom from a right DG action. -/
def leftShiftInv
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) : shiftedSourceLeft N rho k ⟶ shiftedLeft N rho k where
  hom n :=
    (Cochain.leftShiftLinearEquiv R M N (n - k) k n (sub_add_cancel n k)).symm.toLinearMap
  comm_d := sorry
  comm_smul := sorry

/-- The degree-`n` component of the inverse first-variable shift map from a right action is the
inverse linear shift equivalence. -/
@[simp]
theorem leftShiftInv_hom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k n : ℤ) :
    (leftShiftInv N rho k).hom n =
      (Cochain.leftShiftLinearEquiv R M N (n - k) k n
        (sub_add_cancel n k)).symm.toLinearMap := sorry

/-- The fixed-underlying first-variable shift isomorphism induced by a right DG action. -/
def leftShiftIso
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M))
    (k : ℤ) : shiftedLeft N rho k ≅ shiftedSourceLeft N rho k where
  hom := leftShiftHom N rho k
  inv := leftShiftInv N rho k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the first-variable shift isomorphism from a right action is
`leftShiftHom`. -/
@[simp]
theorem leftShiftIso_hom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M)) (k : ℤ) :
    (leftShiftIso N rho k).hom = leftShiftHom N rho k := sorry

/-- The inverse map of the first-variable shift isomorphism from a right action is
`leftShiftInv`. -/
@[simp]
theorem leftShiftIso_inv
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (underlyingDifferential M)) (k : ℤ) :
    (leftShiftIso N rho k).inv = leftShiftInv N rho k := sorry

namespace Action

/-- The left DG module on `Hom^•(M, N)` induced by a genuine right action on `M`. -/
abbrev left
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.ActionOn A M) :
    LeftDifferentialGradedModule A :=
  OfRight.left N rho.toFixed

/-- The canonical left-DG-module shift of the internal Hom induced by a genuine right action. -/
abbrev shiftedLeft
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.ActionOn A M) (k : ℤ) :
    LeftDifferentialGradedModule A :=
  OfRight.shiftedLeft N rho.toFixed k

/-- The left DG module on `Hom^•(M⟦k⟧, N)` induced by the shifted genuine right action. -/
abbrev shiftedSourceLeft
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.ActionOn A M) (k : ℤ) :
    LeftDifferentialGradedModule A :=
  OfRight.shiftedSourceLeft N rho.toFixed k

/-- The forward first-variable shift map induced by a genuine right DG action. -/
abbrev shiftHom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.ActionOn A M) (k : ℤ) :
    shiftedLeft N rho k ⟶ shiftedSourceLeft N rho k :=
  OfRight.leftShiftHom N rho.toFixed k

/-- The inverse first-variable shift map induced by a genuine right DG action. -/
abbrev shiftInv
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.ActionOn A M) (k : ℤ) :
    shiftedSourceLeft N rho k ⟶ shiftedLeft N rho k :=
  OfRight.leftShiftInv N rho.toFixed k

/-- Remark 22.13.7 (0FQ9) (3): first-variable shift is an isomorphism of left differential
graded modules when the source carries a genuine right DG action. -/
@[stacks 0FQ9 "first-variable shift isomorphism from a right DG action"]
def shiftIso
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.ActionOn A M) (k : ℤ) :
    shiftedLeft N rho k ≅ shiftedSourceLeft N rho k :=
  OfRight.leftShiftIso N rho.toFixed k

/-- The forward map of `shiftIso` is `shiftHom`. -/
@[simp]
theorem shiftIso_hom
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.ActionOn A M) (k : ℤ) :
    (shiftIso N rho k).hom = shiftHom N rho k := sorry

/-- The inverse map of `shiftIso` is `shiftInv`. -/
@[simp]
theorem shiftIso_inv
    {A : CochainDGAlgebra.{u, v} R} {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (rho : DifferentialGradedModule.ActionOn A M) (k : ℤ) :
    (shiftIso N rho k).inv = shiftInv N rho k := sorry

end Action

end OfRight

end DifferentialGradedModule.InternalHom
