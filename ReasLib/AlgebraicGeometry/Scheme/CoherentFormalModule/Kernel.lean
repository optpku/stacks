/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

/-!
# Kernels of coherent formal modules

For a map of coherent formal modules, take its kernel on inverse-limit sheaves and quotient
by successive ideal powers. On an affine open this is the system `K / I ^ n K`, where `K` is
the kernel of the corresponding map of finite modules over the completed ring. This is also
the stable-quotient construction in Stacks tag 087X; the system of stagewise kernels generally
fails the formal-module quotient condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The ideal power acts trivially on the projection to the corresponding formal stage. -/
theorem powerAction_stageProjection (F : CoherentFormalModules X I) (n : ℕ) :
    powerAction.{u, u, u} I.toSubobject (limitModule F) n ≫ stageProjection F n = 0 := sorry

/-- The canonical comparison from the quotient of the inverse limit to the formal stage. -/
def quotientComparison (F : CoherentFormalModules X I) (n : ℕ) :
    PowerQuotientModule.stage.{u, u, u} I.toSubobject (limitModule F) n ⟶
      (F.obj.obj (op n)).obj :=
  cokernel.desc (powerAction.{u, u, u} I.toSubobject (limitModule F) n)
    (stageProjection F n) (powerAction_stageProjection F n)

/-- A coherent formal module is recovered from the ideal-power quotients of its inverse limit. -/
instance quotientComparison_isIso [IsNoetherian X] (F : CoherentFormalModules X I) (n : ℕ) :
    IsIso (quotientComparison F n) := sorry

/-- The quotient comparison carries the canonical quotient projection to the limit projection. -/
@[reassoc (attr := simp)]
theorem projection_quotientComparison (F : CoherentFormalModules X I) (n : ℕ) :
    PowerQuotientModule.projection.{u, u, u} I.toSubobject (limitModule F) n ≫
        quotientComparison F n = stageProjection F n := sorry

namespace Kernel

variable {F G : CoherentFormalModules X I} (f : F ⟶ G)

/-- The module sheaf kernel of the induced map on inverse limits. This sheaf need not be
coherent over the original scheme; its ideal-power quotients are coherent. -/
abbrev limitKernel : X.Modules :=
  Limits.kernel ((limitFunctor I).map f)

/-- The module sheaf underlying stage `n` of the internal kernel. -/
abbrev Stage (n : ℕ) : X.Modules :=
  PowerQuotientModule.stage.{u, u, u} I.toSubobject (limitKernel f) n

section LimitLift

variable {H : CoherentFormalModules X I} (g : H ⟶ F) (w : g ≫ f = 0)

/-- A map killed by `f` induces a map into the kernel on inverse limits. -/
theorem limitMap_condition (w : g ≫ f = 0) : (limitFunctor I).map g ≫ (limitFunctor I).map f = 0 := sorry

/-- The induced map on limit-module kernels, defined by the ordinary module-sheaf kernel lift. -/
def moduleLift : limitModule H ⟶ limitKernel f :=
  Limits.kernel.lift ((limitFunctor I).map f) ((limitFunctor I).map g)
    (limitMap_condition f g w)

end LimitLift

/-- The ideal-power quotients of the limit kernel are coherent. -/
theorem stage_isCoherent [IsNoetherian X] (n : ℕ) : (Stage f n).IsCoherent := sorry

variable [IsNoetherian X]

/-- Stage `n` of the internal kernel, bundled as a coherent module sheaf. -/
def stage (n : ℕ) : RingedSpace.Coh X.toRingedSpace :=
  ⟨Stage f n, stage_isCoherent f n⟩

/-- The transition between successive ideal-power quotients of the limit kernel. -/
def step (n : ℕ) : stage f (n + 1) ⟶ stage f n :=
  ObjectProperty.homMk (PowerQuotientModule.step.{u, u, u} I.toSubobject (limitKernel f) n)

/-- The inverse system of ideal-power quotients of the limit kernel. -/
def system : SequentialInverseSystem (RingedSpace.Coh X.toRingedSpace) :=
  Functor.ofOpSequence (step f)

/-- The internal kernel satisfies the coherent formal module conditions. -/
theorem system_mem : IsCoherentFormalModuleSystem I (system f) := sorry

/-- The coherent formal module kernel of `f`. -/
@[stacks 087X "internal kernel object"]
def obj : CoherentFormalModules X I :=
  ⟨system f, system_mem f⟩

/-- The underlying module sheaf of an internal kernel stage is its canonical ideal-power quotient. -/
@[simp]
theorem obj_stage (n : ℕ) : ((obj f).obj.obj (op n)).obj = Stage f n := sorry

/-- The limit kernel projection factors through its quotient at the corresponding stage. -/
theorem powerAction_projection (n : ℕ) :
    powerAction.{u, u, u} I.toSubobject (limitKernel f) n ≫
        (Limits.kernel.ι ((limitFunctor I).map f) ≫ stageProjection F n) = 0 := sorry

/-- The canonical map from an internal kernel stage into the source stage. -/
def stageι (n : ℕ) : stage f n ⟶ F.obj.obj (op n) :=
  ObjectProperty.homMk
    (cokernel.desc (powerAction.{u, u, u} I.toSubobject (limitKernel f) n)
      (Limits.kernel.ι ((limitFunctor I).map f) ≫ stageProjection F n)
      (powerAction_projection f n))

/-- The stage inclusions commute with inverse-system transitions. -/
theorem stageι_naturality (n : ℕ) :
    (system f).stepMap n ≫ stageι f n =
      stageι f (n + 1) ≫ F.obj.stepMap n := sorry

/-- The natural map from the internal kernel system into the source system. -/
def systemι : system f ⟶ F.obj :=
  NatTrans.ofOpSequence (stageι f) (stageι_naturality f)

/-- The inclusion of the internal kernel into its source formal module. -/
@[stacks 087X "internal kernel inclusion"]
def ι : obj f ⟶ F :=
  ObjectProperty.homMk (systemι f)

/-- The component of the internal kernel inclusion is the canonical stage inclusion. -/
@[simp]
theorem ι_app (n : ℕ) : ((ι f).hom.app (op n)).hom = (stageι f n).hom := sorry

/-- The kernel inclusion followed by the original map is zero. -/
@[reassoc (attr := simp)]
theorem condition : ι f ≫ f = 0 := sorry

variable {H : CoherentFormalModules X I} (g : H ⟶ F) (w : g ≫ f = 0)

/-- The universal lift at a formal stage. The inverse of the canonical quotient comparison
identifies the source stage with its limit quotient before applying the quotient of the lift. -/
def stageLift (n : ℕ) : H.obj.obj (op n) ⟶ stage f n :=
  ObjectProperty.homMk
    (inv (quotientComparison H n) ≫
      PowerQuotientModule.map.{u, u, u} I.toSubobject (moduleLift f g w) n)

/-- Stage lifts commute with inverse-system transitions. -/
theorem stageLift_naturality (n : ℕ) :
    H.obj.stepMap n ≫ stageLift f g w n =
      stageLift f g w (n + 1) ≫ (system f).stepMap n := sorry

/-- The universal lift as a map of inverse systems. -/
def systemLift : H.obj ⟶ system f :=
  NatTrans.ofOpSequence (stageLift f g w) (stageLift_naturality f g w)

/-- The universal lift into the internal formal-module kernel. -/
@[stacks 087X "internal kernel universal lift"]
def lift : H ⟶ obj f :=
  ObjectProperty.homMk (systemLift f g w)

/-- The component of the universal lift is the canonical quotient of the limit-module lift. -/
@[simp]
theorem lift_app (n : ℕ) : ((lift f g w).hom.app (op n)).hom = (stageLift f g w n).hom := sorry

/-- The universal lift factors the given map. -/
@[reassoc (attr := simp)]
theorem lift_ι : lift f g w ≫ ι f = g := sorry

/-- A map into the internal kernel is determined by its composition with the inclusion. -/
theorem lift_unique (m : H ⟶ obj f) (hm : m ≫ ι f = g) :
    m = lift f g w := sorry

/-- The kernel fork carries the explicit universal lift. -/
@[stacks 087X "internal kernel universal property"]
def isLimit : IsLimit (KernelFork.ofι (ι f) (condition f)) :=
  KernelFork.IsLimit.ofι (ι f) (condition f) (lift f) (lift_ι f) (lift_unique f)

/-- The stage projection from the limit kernel agrees with the kernel-stage inclusion. -/
@[reassoc (attr := simp)]
theorem projection_stageι (n : ℕ) :
    PowerQuotientModule.projection.{u, u, u} I.toSubobject (limitKernel f) n ≫ (stageι f n).hom =
      Limits.kernel.ι ((limitFunctor I).map f) ≫ stageProjection F n := sorry

end Kernel

/-- Coherent formal modules have internal kernels. The inclusion into all inverse systems
of coherent sheaves generally does not preserve these kernels. -/
instance hasKernels [IsNoetherian X] (I : X.IdealSheafData) : HasKernels (CoherentFormalModules X I) where
  has_limit f := ⟨⟨⟨KernelFork.ofι (Kernel.ι f) (Kernel.condition f), Kernel.isLimit f⟩⟩⟩

end AlgebraicGeometry.Scheme.CoherentFormalModules
