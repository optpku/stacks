/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison

/-!
# The graded algebra of integral powers of an invertible module

The integral tensor powers of an invertible module sheaf carry canonical unit and multiplication
maps.  Evaluating those maps on local sections gives a coherent `ℤ`-graded algebra sheaf.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.InvertiblePower

variable {X : RingedSpace.{u}}

/-- The canonical unit section of the zeroth integral power. -/
noncomputable def oneSection
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) :
    (L ^⊗ (0 : ℤ)).val.obj U :=
  (((zeroIso L).inv.val.app U).hom) (1 : X.sheaf.obj.obj U)

/-- Multiplication of local sections of two integral powers. -/
noncomputable def mulSection
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) (m n : ℤ)
    (x : (L ^⊗ m).val.obj U) (y : (L ^⊗ n).val.obj U) :
    (L ^⊗ (m + n)).val.obj U :=
  (((addIso L m n).hom.val.app U).hom) (tensorSection X.sheaf U x y)

/-- Multiplication of integral-power sections is additive in the right argument. -/
theorem mulSection_add_right
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) (m n : ℤ)
    (x : (L ^⊗ m).val.obj U) (y y' : (L ^⊗ n).val.obj U) :
    mulSection L U m n x (y + y') =
      mulSection L U m n x y + mulSection L U m n x y' := sorry

/-- Multiplication of integral-power sections is linear in the right argument. -/
theorem mulSection_smul_right
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) (m n : ℤ)
    (x : (L ^⊗ m).val.obj U) (r : X.sheaf.obj.obj U)
    (y : (L ^⊗ n).val.obj U) :
    mulSection L U m n x (r • y) =
      (RingHom.id (X.sheaf.obj.obj U)) r • mulSection L U m n x y := sorry

/-- Right-linear multiplication by a fixed integral-power section. -/
noncomputable def mulSectionRight
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) (m n : ℤ)
    (x : (L ^⊗ m).val.obj U) :
    (L ^⊗ n).val.obj U →ₗ[X.sheaf.obj.obj U] (L ^⊗ (m + n)).val.obj U where
  toFun := mulSection L U m n x
  map_add' := mulSection_add_right L U m n x
  map_smul' := mulSection_smul_right L U m n x

/-- Right-linear multiplication is additive in its fixed left argument. -/
theorem mulSectionRight_add
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) (m n : ℤ)
    (x x' : (L ^⊗ m).val.obj U) :
    mulSectionRight L U m n (x + x') =
      mulSectionRight L U m n x + mulSectionRight L U m n x' := sorry

/-- Right-linear multiplication is linear in its fixed left argument. -/
theorem mulSectionRight_smul
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) (m n : ℤ)
    (r : X.sheaf.obj.obj U) (x : (L ^⊗ m).val.obj U) :
    mulSectionRight L U m n (r • x) = r • mulSectionRight L U m n x := sorry

/-- The bilinear multiplication of local sections of integral powers. -/
noncomputable def mulSectionLinear
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) (m n : ℤ) :
    (L ^⊗ m).val.obj U →ₗ[X.sheaf.obj.obj U]
      (L ^⊗ n).val.obj U →ₗ[X.sheaf.obj.obj U] (L ^⊗ (m + n)).val.obj U where
  toFun := mulSectionRight L U m n
  map_add' := mulSectionRight_add L U m n
  map_smul' := mulSectionRight_smul L U m n

/-- The canonical unit section commutes with restriction maps. -/
theorem oneSection_map
    (L : X.Modules) [isInvertibleObject L] {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ((L ^⊗ (0 : ℤ)).val.map i).hom (oneSection L U) = oneSection L V := sorry

/-- Multiplication of integral-power sections commutes with restriction maps. -/
theorem mulSection_map
    (L : X.Modules) [isInvertibleObject L] {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (m n : ℤ) (x : (L ^⊗ m).val.obj U) (y : (L ^⊗ n).val.obj U) :
    ((L ^⊗ (m + n)).val.map i).hom (mulSection L U m n x y) =
      mulSection L V m n (((L ^⊗ m).val.map i).hom x)
        (((L ^⊗ n).val.map i).hom y) := sorry

/-- Multiplication of integral-power sections is associative. -/
theorem mulSection_assoc
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) (i j k : ℤ)
    (a : (L ^⊗ i).val.obj U) (b : (L ^⊗ j).val.obj U)
    (c : (L ^⊗ k).val.obj U) :
    HEq (mulSection L U (i + j) k (mulSection L U i j a b) c)
      (mulSection L U i (j + k) a (mulSection L U j k b c)) := sorry

/-- The canonical zeroth-power section is a left unit. -/
theorem oneSection_mul
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) (n : ℤ)
    (a : (L ^⊗ n).val.obj U) :
    HEq (mulSection L U 0 n (oneSection L U) a) a := sorry

/-- The canonical zeroth-power section is a right unit. -/
theorem mulSection_one
    (L : X.Modules) [isInvertibleObject L] (U : (Opens X)ᵒᵖ) (n : ℤ)
    (a : (L ^⊗ n).val.obj U) :
    HEq (mulSection L U n 0 a (oneSection L U)) a := sorry

/-- The integral tensor powers of an invertible module form a `ℤ`-graded algebra sheaf. -/
noncomputable def gradedAlgebra
    (L : X.Modules) [isInvertibleObject L] :
    SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} X.sheaf ℤ where
  obj := fun n ↦ L ^⊗ n
  one := oneSection L
  mul := mulSectionLinear L
  map_one := oneSection_map L
  map_mul := mulSection_map L
  mul_assoc := mulSection_assoc L
  one_mul := oneSection_mul L
  mul_one := mulSection_one L

end AlgebraicGeometry.RingedSpace.InvertiblePower
