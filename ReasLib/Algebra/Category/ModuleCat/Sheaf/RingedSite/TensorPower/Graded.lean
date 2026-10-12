/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Monoid
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The graded tensor algebra on a ringed site

The tensor-power sheaves, concatenation morphisms, and degree-zero section assemble into an
`ℕ`-graded algebra sheaf.  This is the sectionwise presentation used by local-section APIs;
`TensorPower.Monoid` owns the canonical Mathlib `Mon (GradedObject ...)` presentation.  The
construction is topology-independent and does not install any local monoidal or module instances.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The degree-zero unit as a local section of the zeroth tensor-power sheaf. -/
@[stacks 01CF "degree-zero section of the graded tensor algebra"]
noncomputable def oneSection
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) :
    (sheaf 𝒪 F 0).val.obj U :=
  ((one 𝒪 F).val.app U).hom (1 : 𝒪.obj.obj U)

/-- The product of homogeneous tensor-power sections. -/
@[stacks 01CF "homogeneous tensor-power section multiplication"]
noncomputable def mulSection
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf 𝒪 F n).val.obj U) (y : (sheaf 𝒪 F m).val.obj U) :
    (sheaf 𝒪 F (n + m)).val.obj U :=
  ((mul 𝒪 F n m).val.app U).hom (tensorSection 𝒪 U x y)

/-- Tensor-power multiplication on sections is additive in the right argument. -/
@[stacks 01CF "additivity of homogeneous tensor multiplication"]
theorem mulSection_add_right
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf 𝒪 F n).val.obj U)
    (y y' : (sheaf 𝒪 F m).val.obj U) :
    mulSection 𝒪 F U n m x (y + y') =
      mulSection 𝒪 F U n m x y + mulSection 𝒪 F U n m x y' := sorry

/-- Tensor-power multiplication on sections is linear in the right argument. -/
@[stacks 01CF "linearity of homogeneous tensor multiplication"]
theorem mulSection_smul_right
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf 𝒪 F n).val.obj U) (r : 𝒪.obj.obj U)
    (y : (sheaf 𝒪 F m).val.obj U) :
    mulSection 𝒪 F U n m x (r • y) =
      (RingHom.id (𝒪.obj.obj U)) r • mulSection 𝒪 F U n m x y := sorry

/-- Right-linear multiplication by a fixed homogeneous tensor-power section. -/
@[stacks 01CF "right-linear homogeneous tensor multiplication"]
noncomputable def mulSectionRight
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf 𝒪 F n).val.obj U) :
    (sheaf 𝒪 F m).val.obj U →ₗ[𝒪.obj.obj U]
      (sheaf 𝒪 F (n + m)).val.obj U where
  toFun := mulSection 𝒪 F U n m x
  map_add' := mulSection_add_right 𝒪 F U n m x
  map_smul' := mulSection_smul_right 𝒪 F U n m x

/-- Right-linear tensor-power multiplication is additive in its fixed left argument. -/
@[stacks 01CF "left additivity of homogeneous tensor multiplication"]
theorem mulSectionRight_add
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (x x' : (sheaf 𝒪 F n).val.obj U) :
    mulSectionRight 𝒪 F U n m (x + x') =
      mulSectionRight 𝒪 F U n m x + mulSectionRight 𝒪 F U n m x' := sorry

/-- Right-linear tensor-power multiplication is linear in its fixed left argument. -/
@[stacks 01CF "left linearity of homogeneous tensor multiplication"]
theorem mulSectionRight_smul
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (r : 𝒪.obj.obj U) (x : (sheaf 𝒪 F n).val.obj U) :
    mulSectionRight 𝒪 F U n m (r • x) =
      r • mulSectionRight 𝒪 F U n m x := sorry

/-- The bilinear multiplication on local sections of homogeneous tensor powers. -/
@[stacks 01CF "bilinear homogeneous tensor multiplication"]
noncomputable def mulSectionLinear
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ) :
    (sheaf 𝒪 F n).val.obj U →ₗ[𝒪.obj.obj U]
      (sheaf 𝒪 F m).val.obj U →ₗ[𝒪.obj.obj U]
        (sheaf 𝒪 F (n + m)).val.obj U where
  toFun := mulSectionRight 𝒪 F U n m
  map_add' := mulSectionRight_add 𝒪 F U n m
  map_smul' := mulSectionRight_smul 𝒪 F U n m

/-- The degree-zero tensor-power section commutes with restriction maps. -/
@[stacks 01CF "restriction of the graded tensor unit section"]
theorem oneSection_map
    (F : ringedSiteModuleCategory J 𝒪) {U V : Cᵒᵖ} (i : U ⟶ V) :
    ((sheaf 𝒪 F 0).val.map i).hom (oneSection 𝒪 F U) = oneSection 𝒪 F V := sorry

/-- Homogeneous tensor-power multiplication commutes with restriction maps. -/
@[stacks 01CF "restriction of homogeneous tensor multiplication"]
theorem mulSection_map
    (F : ringedSiteModuleCategory J 𝒪) {U V : Cᵒᵖ} (i : U ⟶ V)
    (n m : ℕ) (x : (sheaf 𝒪 F n).val.obj U)
    (y : (sheaf 𝒪 F m).val.obj U) :
    ((sheaf 𝒪 F (n + m)).val.map i).hom (mulSection 𝒪 F U n m x y) =
      mulSection 𝒪 F V n m (((sheaf 𝒪 F n).val.map i).hom x)
        (((sheaf 𝒪 F m).val.map i).hom y) := sorry

/-- Homogeneous tensor-power multiplication is associative on local sections. -/
@[stacks 01CF "sectionwise associativity of tensor multiplication"]
theorem mulSection_assoc
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (i j k : ℕ)
    (a : (sheaf 𝒪 F i).val.obj U) (b : (sheaf 𝒪 F j).val.obj U)
    (c : (sheaf 𝒪 F k).val.obj U) :
    HEq (mulSection 𝒪 F U (i + j) k (mulSection 𝒪 F U i j a b) c)
      (mulSection 𝒪 F U i (j + k) a (mulSection 𝒪 F U j k b c)) := sorry

/-- The degree-zero tensor-power section is a left unit. -/
@[stacks 01CF "sectionwise left unit law"]
theorem oneSection_mul
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n : ℕ)
    (a : (sheaf 𝒪 F n).val.obj U) :
    HEq (mulSection 𝒪 F U 0 n (oneSection 𝒪 F U) a) a := sorry

/-- The degree-zero tensor-power section is a right unit. -/
@[stacks 01CF "sectionwise right unit law"]
theorem mulSection_one
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n : ℕ)
    (a : (sheaf 𝒪 F n).val.obj U) :
    HEq (mulSection 𝒪 F U n 0 a (oneSection 𝒪 F U)) a := sorry

/-- The tensor powers of `F` form their canonical naturally graded tensor algebra sheaf. -/
@[stacks 01CF "graded tensor algebra on a ringed site"]
noncomputable def graded
    (F : ringedSiteModuleCategory J 𝒪) : GradedAlgebraSheaf 𝒪 ℕ where
  obj := sheaf 𝒪 F
  one := oneSection 𝒪 F
  mul := mulSectionLinear 𝒪 F
  map_one := oneSection_map 𝒪 F
  map_mul := mulSection_map 𝒪 F
  mul_assoc := mulSection_assoc 𝒪 F
  one_mul := oneSection_mul 𝒪 F
  mul_one := mulSection_one 𝒪 F

/-- The degree-`n` object of the graded tensor algebra is the degree-`n` tensor-power sheaf. -/
@[simp, stacks 01CF "graded tensor algebra component"]
theorem graded_obj
    (F : ringedSiteModuleCategory J 𝒪) (n : ℕ) :
    (graded 𝒪 F).obj n = sheaf 𝒪 F n := sorry

/-- The Mathlib monoid-object and sectionwise presentations have the same underlying graded
module sheaf. -/
@[stacks 01CF "comparison of graded tensor-algebra presentations"]
theorem mon_X_eq_graded
    (F : ringedSiteModuleCategory J 𝒪) :
    (mon 𝒪 F).X = (graded 𝒪 F).toGradedObject := sorry

end SheafOfModules.RingedSite.TensorPower
