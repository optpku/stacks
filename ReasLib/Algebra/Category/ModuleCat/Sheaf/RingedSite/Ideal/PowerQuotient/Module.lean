module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Ideal-power quotients of module sheaves

The cokernels of the canonical ideal-power actions on a module sheaf form an inverse system.
This module also records the induced maps between quotients and the corresponding system of
global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

/-- The quotient module sheaf `M / I ^ n M`, presented as the cokernel of the canonical action
of the `n`th tensor power of `I` on `M`. -/
noncomputable abbrev stage
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℕ) :
    ringedSiteModuleCategory.{u, v, w, w} J O :=
  cokernel (powerAction I M n)

/-- The canonical projection `M ⟶ M / I ^ n M`. -/
noncomputable abbrev projection
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℕ) :
    M ⟶ stage I M n :=
  cokernel.π (powerAction I M n)

/-- A morphism of module sheaves induces a morphism between their quotients by `I ^ n`. -/
noncomputable def map
    (I : Subobject (unitModule J O))
    {M N : ringedSiteModuleCategory.{u, v, w, w} J O} (f : M ⟶ N) (n : ℕ) :
    stage I M n ⟶ stage I N n :=
  cokernel.desc (powerAction I M n) (f ≫ projection I N n) (by
    have h := powerAction_naturality I n f
    change ((TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) ◁ f) ≫
        powerAction I N n = powerAction I M n ≫ f at h
    rw [← Category.assoc, ← h, Category.assoc, cokernel.condition, comp_zero])

/-- The quotient projection is natural in the module. -/
@[reassoc]
theorem projection_comp_map
    (I : Subobject (unitModule J O))
    {M N : ringedSiteModuleCategory.{u, v, w, w} J O} (f : M ⟶ N) (n : ℕ) :
    projection I M n ≫ map I f n = f ≫ projection I N n := by
  apply cokernel.π_desc

private noncomputable def powerFactor
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℕ) :
    tensorObj
        (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) (n + 1)) M ⟶
      tensorObj
        (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M :=
  (α_ (I : ringedSiteModuleCategory J O)
      (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M).hom ≫
    action I (tensorObj
      (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M)

private theorem powerFactor_comp_powerAction
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℕ) :
    powerFactor I M n ≫ powerAction I M n = powerAction I M (n + 1) := by
  have h := action_naturality I (powerAction I M n)
  change ((I : ringedSiteModuleCategory J O) ◁ powerAction I M n) ≫ action I M =
    action I (tensorObj
      (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M) ≫
      powerAction I M n at h
  rw [powerAction_succ]
  dsimp only [powerFactor]
  simp only [Category.assoc]
  exact congrArg
    (fun k ↦ (α_ (I : ringedSiteModuleCategory J O)
      (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M).hom ≫ k)
    h.symm

/-- The transition `M / I ^ (n + 1) M ⟶ M / I ^ n M`. -/
noncomputable def step
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℕ) :
    stage I M (n + 1) ⟶ stage I M n :=
  cokernel.desc (powerAction I M (n + 1)) (projection I M n) (by
    rw [← powerFactor_comp_powerAction I M n]
    simp [Category.assoc])

/-- The successor quotient projection followed by the transition is the preceding quotient
projection. -/
@[reassoc]
theorem projection_comp_step
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℕ) :
    projection I M (n + 1) ≫ step I M n = projection I M n := by
  apply cokernel.π_desc

/-- The inverse system `n ↦ M / I ^ n M`. -/
noncomputable def system
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) :
    ℕᵒᵖ ⥤ ringedSiteModuleCategory.{u, v, w, w} J O :=
  Functor.ofOpSequence (step I M)

/-- The inverse system `n ↦ H⁰(M / I ^ n M)` of global sections. -/
noncomputable def sectionsSystem
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) : ℕᵒᵖ ⥤ Type (max u w) :=
  system I M ⋙ SheafOfModules.sectionsFunctor (ringSheaf J O)

end SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule
