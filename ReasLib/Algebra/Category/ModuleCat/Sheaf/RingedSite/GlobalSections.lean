/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite

@[expose] public section

open CategoryTheory

namespace SheafOfModules.RingedSite.GlobalSections

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable {O : Sheaf J CommRingCat.{u}}

/-- Pointwise multiplication of global structure-sheaf sections commutes with restriction. -/
theorem mulNaturality (g f : (unitModule J O).sections) (U V : Cᵒᵖ) (i : U ⟶ V) :
    (unitModule J O).val.map i (Mul.mul (α := O.obj.obj U) (g.val U) (f.val U)) =
      Mul.mul (α := O.obj.obj V) (g.val V) (f.val V) := sorry

/-- The global section obtained by multiplying two compatible families pointwise. -/
noncomputable def mul (g f : (unitModule J O).sections) : (unitModule J O).sections :=
  PresheafOfModules.sectionsMk (fun U ↦ Mul.mul (α := O.obj.obj U) (g.val U) (f.val U))
    (fun {U V} i ↦ mulNaturality g f U V i)

/-- Evaluation of a product of global sections is the product of their evaluations. -/
theorem mul_apply (g f : (unitModule J O).sections) (U : Cᵒᵖ) :
    (mul g f).val U = Mul.mul (α := O.obj.obj U) (g.val U) (f.val U) := sorry

end SheafOfModules.RingedSite.GlobalSections
