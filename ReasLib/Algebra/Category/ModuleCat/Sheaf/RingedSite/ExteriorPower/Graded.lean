/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The graded exterior algebra on a ringed site

The degreewise exterior-power sheaves, their fixed-degree multiplication morphisms, and the
degree-zero unit assemble into a naturally graded algebra sheaf.  All data are inherited from
the corresponding universal constructions before sheafification.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The degree-zero unit as a local section of `Λ⁰(F)`. -/
noncomputable def oneSection
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) :
    (sheaf 𝒪 F 0).val.obj U :=
  ((one 𝒪 F).val.app U).hom (1 : 𝒪.obj.obj U)

/-- The local product of homogeneous exterior-power sections, induced by the canonical tensor
section and the fixed-degree multiplication morphism. -/
noncomputable def mulSection
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf 𝒪 F n).val.obj U) (y : (sheaf 𝒪 F m).val.obj U) :
    (sheaf 𝒪 F (n + m)).val.obj U :=
  ((mul 𝒪 F n m).val.app U).hom
    (tensorSection 𝒪 U x y)

/-- Exterior multiplication on local sections is additive in the right argument. -/
theorem mulSection_add_right
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf 𝒪 F n).val.obj U)
    (y y' : (sheaf 𝒪 F m).val.obj U) :
    mulSection 𝒪 F U n m x (y + y') =
      mulSection 𝒪 F U n m x y + mulSection 𝒪 F U n m x y' := sorry

/-- Exterior multiplication on local sections is linear in the right argument. -/
theorem mulSection_smul_right
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf 𝒪 F n).val.obj U) (r : 𝒪.obj.obj U)
    (y : (sheaf 𝒪 F m).val.obj U) :
    mulSection 𝒪 F U n m x (r • y) =
      (RingHom.id (𝒪.obj.obj U)) r • mulSection 𝒪 F U n m x y := sorry

/-- Right-linear multiplication by a fixed homogeneous exterior-power section. -/
noncomputable def mulSectionRight
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf 𝒪 F n).val.obj U) :
    (sheaf 𝒪 F m).val.obj U →ₗ[𝒪.obj.obj U]
      (sheaf 𝒪 F (n + m)).val.obj U where
  toFun := mulSection 𝒪 F U n m x
  map_add' := mulSection_add_right 𝒪 F U n m x
  map_smul' := mulSection_smul_right 𝒪 F U n m x

/-- Right-linear exterior multiplication is additive in its fixed left argument. -/
theorem mulSectionRight_add
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (x x' : (sheaf 𝒪 F n).val.obj U) :
    mulSectionRight 𝒪 F U n m (x + x') =
      mulSectionRight 𝒪 F U n m x + mulSectionRight 𝒪 F U n m x' := sorry

/-- Right-linear exterior multiplication is linear in its fixed left argument. -/
theorem mulSectionRight_smul
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (r : 𝒪.obj.obj U) (x : (sheaf 𝒪 F n).val.obj U) :
    mulSectionRight 𝒪 F U n m (r • x) =
      r • mulSectionRight 𝒪 F U n m x := sorry

/-- The bilinear multiplication on local sections of two homogeneous exterior powers. -/
noncomputable def mulSectionLinear
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ) :
    (sheaf 𝒪 F n).val.obj U →ₗ[𝒪.obj.obj U]
      (sheaf 𝒪 F m).val.obj U →ₗ[𝒪.obj.obj U]
        (sheaf 𝒪 F (n + m)).val.obj U where
  toFun := mulSectionRight 𝒪 F U n m
  map_add' := mulSectionRight_add 𝒪 F U n m
  map_smul' := mulSectionRight_smul 𝒪 F U n m

/-- The degree-zero unit section commutes with restriction maps. -/
theorem oneSection_map
    (F : ringedSiteModuleCategory J 𝒪) {U V : Cᵒᵖ} (i : U ⟶ V) :
    ((sheaf 𝒪 F 0).val.map i).hom (oneSection 𝒪 F U) =
      oneSection 𝒪 F V := sorry

/-- Homogeneous exterior multiplication commutes with restriction maps. -/
theorem mulSection_map
    (F : ringedSiteModuleCategory J 𝒪) {U V : Cᵒᵖ} (i : U ⟶ V)
    (n m : ℕ) (x : (sheaf 𝒪 F n).val.obj U)
    (y : (sheaf 𝒪 F m).val.obj U) :
    ((sheaf 𝒪 F (n + m)).val.map i).hom (mulSection 𝒪 F U n m x y) =
      mulSection 𝒪 F V n m
        (((sheaf 𝒪 F n).val.map i).hom x)
        (((sheaf 𝒪 F m).val.map i).hom y) := sorry

/-- Homogeneous exterior multiplication is associative on local sections. -/
theorem mulSection_assoc
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (i j k : ℕ)
    (a : (sheaf 𝒪 F i).val.obj U) (b : (sheaf 𝒪 F j).val.obj U)
    (c : (sheaf 𝒪 F k).val.obj U) :
    HEq (mulSection 𝒪 F U (i + j) k (mulSection 𝒪 F U i j a b) c)
      (mulSection 𝒪 F U i (j + k) a (mulSection 𝒪 F U j k b c)) := sorry

/-- The degree-zero exterior section is a left unit. -/
theorem oneSection_mul
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n : ℕ)
    (a : (sheaf 𝒪 F n).val.obj U) :
    HEq (mulSection 𝒪 F U 0 n (oneSection 𝒪 F U) a) a := sorry

/-- The degree-zero exterior section is a right unit. -/
theorem mulSection_one
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n : ℕ)
    (a : (sheaf 𝒪 F n).val.obj U) :
    HEq (mulSection 𝒪 F U n 0 a (oneSection 𝒪 F U)) a := sorry

/-- The exterior powers of `F`, with their canonical unit and multiplication, form a naturally
graded algebra sheaf. -/
@[stacks 01CF "graded exterior algebra on a ringed site"]
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

/-- Homogeneous exterior multiplication satisfies the Koszul sign rule. -/
theorem mulSection_comm
    (F : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) (n m : ℕ)
    (a : (sheaf 𝒪 F n).val.obj U) (b : (sheaf 𝒪 F m).val.obj U) :
    HEq (mulSection 𝒪 F U n m a b)
      ((-1 : 𝒪.obj.obj U) ^ (n * m) • mulSection 𝒪 F U m n b a) := sorry

/-- The graded exterior algebra is graded commutative. -/
@[stacks 01CF "graded commutativity of the exterior algebra"]
instance graded_isGradedCommutative
    (F : ringedSiteModuleCategory J 𝒪) :
    (graded 𝒪 F).IsGradedCommutative where
  mul_comm := mulSection_comm 𝒪 F

end SheafOfModules.RingedSite.ExteriorPower
