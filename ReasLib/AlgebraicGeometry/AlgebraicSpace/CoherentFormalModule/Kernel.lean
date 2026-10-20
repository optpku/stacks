/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower.Quotient

/-!
# Internal kernels of coherent formal modules
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace CoherentFormalModules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}

/-- The module-sheaf inverse system underlying a coherent formal module. -/
abbrev moduleSystem (F : CoherentFormalModules X I) : SequentialInverseSystem X.Modules :=
  F.obj ⋙ Coh.inclusion X

/-- The inverse-limit module sheaf of a coherent formal module. -/
abbrev limitModule (F : CoherentFormalModules X I) : X.Modules :=
  limit (moduleSystem F)

/-- The canonical projection of the limit module onto a formal stage. -/
abbrev stageProjection (F : CoherentFormalModules X I) (n : ℕ) :
    limitModule F ⟶ (F.obj.obj (op n)).obj :=
  limit.π (moduleSystem F) (op n)

/-- Taking inverse limits of the underlying module sheaves is functorial. -/
def limitFunctor (I : IdealSubobject X) : CoherentFormalModules X I ⥤ X.Modules :=
  (IsCoherentFormalModuleSystem I).ι ⋙
    (Functor.whiskeringRight ℕᵒᵖ (Coh X) X.Modules).obj (Coh.inclusion X) ⋙ lim

/-- The ideal power vanishes on the projection to the corresponding formal stage. -/
theorem idealPower_stageProjection (F : CoherentFormalModules X I) (n : ℕ) :
    (Modules.idealPowerProductSubobject I (limitModule F) n).arrow ≫ stageProjection F n = 0 := sorry

/-- The canonical comparison from a limit-module quotient to a formal stage. -/
def quotientComparison (F : CoherentFormalModules X I) (n : ℕ) :
    idealPowerQuotient I (limitModule F) n ⟶ (F.obj.obj (op n)).obj :=
  cokernel.desc (Modules.idealPowerProductSubobject I (limitModule F) n).arrow
    (stageProjection F n) (idealPower_stageProjection F n)

/-- Noetherian coherent formal modules are recovered from their limit-module quotients. -/
instance quotientComparison_isIso [IsNoetherian X] [IsQuasiCoherent I]
    (F : CoherentFormalModules X I) (n : ℕ) : IsIso (quotientComparison F n) := sorry

/-- The quotient comparison carries the quotient projection to the limit projection. -/
@[reassoc (attr := simp)]
theorem projection_quotientComparison (F : CoherentFormalModules X I) (n : ℕ) :
    idealPowerQuotient.projection I (limitModule F) n ≫ quotientComparison F n =
      stageProjection F n := sorry

namespace Kernel

variable {F G : CoherentFormalModules X I} (f : F ⟶ G)

/-- The ordinary module-sheaf kernel of the map on inverse limits. -/
abbrev limitKernel : X.Modules := Limits.kernel ((limitFunctor I).map f)

/-- The module sheaf underlying an internal kernel stage. -/
abbrev Stage (n : ℕ) : X.Modules := idealPowerQuotient I (limitKernel f) n

section LimitLift

variable {H : CoherentFormalModules X I} (g : H ⟶ F) (w : g ≫ f = 0)

/-- A zero composite remains zero after taking inverse limits. -/
theorem limitMap_condition (w : g ≫ f = 0) :
    (limitFunctor I).map g ≫ (limitFunctor I).map f = 0 := sorry

/-- The ordinary module-sheaf kernel lift on inverse limits. -/
def moduleLift : limitModule H ⟶ limitKernel f :=
  Limits.kernel.lift ((limitFunctor I).map f) ((limitFunctor I).map g)
    (limitMap_condition f g w)

end LimitLift

/-- Quotients of the limit kernel are coherent for a quasi-coherent ideal on a Noetherian space. -/
theorem stage_isCoherent [IsNoetherian X] [IsQuasiCoherent I] (n : ℕ) :
    (Stage f n).IsCoherent := sorry

variable [IsNoetherian X] [IsQuasiCoherent I]

/-- The internal kernel stage as a coherent module. -/
def stage (n : ℕ) : Coh X := ⟨Stage f n, stage_isCoherent f n⟩

/-- The successor transition of the internal kernel. -/
def step (n : ℕ) : stage f (n + 1) ⟶ stage f n :=
  ObjectProperty.homMk (idealPowerQuotient.step I (limitKernel f) n)

/-- The inverse system of ideal-power quotients of the limit kernel. -/
def system : SequentialInverseSystem (Coh X) := Functor.ofOpSequence (step f)

/-- The quotient system of the limit kernel is a coherent formal module. -/
theorem system_mem : IsCoherentFormalModuleSystem I (system f) := sorry

/-- The internal formal-module kernel. Étale locally its stages are K / I^n K over the completion. -/
@[stacks 089P "internal kernel object"]
def obj : CoherentFormalModules X I := ⟨system f, system_mem f⟩

/-- The underlying sheaf of a kernel stage is the canonical quotient of the limit kernel. -/
@[simp]
theorem obj_stage (n : ℕ) : ((obj f).obj.obj (op n)).obj = Stage f n := sorry

/-- The limit-kernel projection factors through its corresponding quotient. -/
theorem idealPower_projection (n : ℕ) :
    (Modules.idealPowerProductSubobject I (limitKernel f) n).arrow ≫
      (Limits.kernel.ι ((limitFunctor I).map f) ≫ stageProjection F n) = 0 := sorry

/-- The inclusion of an internal kernel stage into the corresponding source stage. -/
def stageι (n : ℕ) : stage f n ⟶ F.obj.obj (op n) :=
  ObjectProperty.homMk
    (cokernel.desc (Modules.idealPowerProductSubobject I (limitKernel f) n).arrow
      (Limits.kernel.ι ((limitFunctor I).map f) ≫ stageProjection F n)
      (idealPower_projection f n))

/-- Stage inclusions commute with inverse-system transitions. -/
theorem stageι_naturality (n : ℕ) :
    (system f).stepMap n ≫ stageι f n = stageι f (n + 1) ≫ F.obj.stepMap n := sorry

/-- The inclusion of the internal kernel as a map of inverse systems. -/
def systemι : system f ⟶ F.obj :=
  NatTrans.ofOpSequence (stageι f) (stageι_naturality f)

/-- The internal kernel inclusion into its source formal module. -/
@[stacks 089P "internal kernel inclusion"]
def ι : obj f ⟶ F := ObjectProperty.homMk (systemι f)

/-- The component of the kernel inclusion is its canonical stage inclusion. -/
@[simp]
theorem ι_app (n : ℕ) : ((ι f).hom.app (op n)).hom = (stageι f n).hom := sorry

/-- The internal kernel inclusion is killed by the original map. -/
@[reassoc (attr := simp)]
theorem condition : ι f ≫ f = 0 := sorry

variable {H : CoherentFormalModules X I} (g : H ⟶ F) (w : g ≫ f = 0)

/-- The stage lift is the quotient of the limit-module lift, through the canonical comparison. -/
def stageLift (n : ℕ) : H.obj.obj (op n) ⟶ stage f n :=
  ObjectProperty.homMk
    (inv (quotientComparison H n) ≫ idealPowerQuotient.map I (moduleLift f g w) n)

/-- Universal stage lifts commute with inverse-system transitions. -/
theorem stageLift_naturality (n : ℕ) :
    H.obj.stepMap n ≫ stageLift f g w n =
      stageLift f g w (n + 1) ≫ (system f).stepMap n := sorry

/-- The universal lift as a map of inverse systems. -/
def systemLift : H.obj ⟶ system f :=
  NatTrans.ofOpSequence (stageLift f g w) (stageLift_naturality f g w)

/-- The universal map into the internal formal-module kernel. -/
@[stacks 089P "internal kernel universal lift"]
def lift : H ⟶ obj f := ObjectProperty.homMk (systemLift f g w)

/-- The component of the universal lift is its canonical stage lift. -/
@[simp]
theorem lift_app (n : ℕ) : ((lift f g w).hom.app (op n)).hom = (stageLift f g w n).hom := sorry

/-- The universal lift factors the given map through the kernel inclusion. -/
@[reassoc (attr := simp)]
theorem lift_ι : lift f g w ≫ ι f = g := sorry

/-- The lift is unique among maps with the required factorization. -/
theorem lift_unique (m : H ⟶ obj f) (hm : m ≫ ι f = g) : m = lift f g w := sorry

/-- The internal kernel fork has the explicit stagewise universal lift. -/
@[stacks 089P "internal kernel universal property"]
def isLimit : IsLimit (KernelFork.ofι (ι f) (condition f)) :=
  KernelFork.IsLimit.ofι (ι f) (condition f) (lift f) (lift_ι f) (lift_unique f)

/-- The kernel-stage projection agrees with the canonical limit-kernel projection. -/
@[reassoc (attr := simp)]
theorem projection_stageι (n : ℕ) :
    idealPowerQuotient.projection I (limitKernel f) n ≫ (stageι f n).hom =
      Limits.kernel.ι ((limitFunctor I).map f) ≫ stageProjection F n := sorry

end Kernel

/-- Coherent formal modules have internal kernels; the ambient stagewise kernel need not be formal. -/
instance hasKernels [IsNoetherian X] (I : IdealSubobject X) [IsQuasiCoherent I] :
    HasKernels (CoherentFormalModules X I) where
  has_limit f := ⟨⟨⟨KernelFork.ofι (Kernel.ι f) (Kernel.condition f), Kernel.isLimit f⟩⟩⟩

end CoherentFormalModules

end AlgebraicGeometry.AlgebraicSpace
