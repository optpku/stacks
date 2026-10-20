/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Data.PNat.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.CategoryTheory.Monoidal.Invertible
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Tactic.CrossRefAttribute

/-!
# Torsion by an ideal sheaf

This file transposes the ideal-power actions into internal Homs.  Their kernels define the
subsheaves annihilated by powers of the ideal, functorially in the module, and their cokernels
define the corresponding quotients by torsion.  Ringed spaces, schemes, and derived
constructions should specialize this API rather than rebuilding it from structure-sheaf notation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.IdealSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The internal-Hom transpose `M ⟶ Hom(I, M)` of the ideal-sheaf action. -/
@[stacks 0GT5 "ideal-sheaf adjoint action"]
noncomputable def actionAdjoint
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) :
    M ⟶ (ihom (I : ringedSiteModuleCategory J O)).obj M :=
  MonoidalClosed.curry (action I M)

/-- Naturality of the adjoint ideal-sheaf action in the module variable. -/
theorem actionAdjoint_naturality
    (I : Subobject (unitModule J O))
    {M N : ringedSiteModuleCategory J O} (f : M ⟶ N) :
    (𝟭 (ringedSiteModuleCategory J O)).map f ≫ actionAdjoint I N =
      actionAdjoint I M ≫
        (ihom (I : ringedSiteModuleCategory J O)).map f := sorry

/-- The adjoint ideal-sheaf action as a natural transformation
`𝟭 Mod(O) ⟶ Hom(I, -)`. -/
@[stacks 0GT5 "adjoint ideal-sheaf action natural transformation"]
noncomputable def actionAdjointNat
    (I : Subobject (unitModule J O)) :
    𝟭 (ringedSiteModuleCategory J O) ⟶
      ihom (I : ringedSiteModuleCategory J O) where
  app M := actionAdjoint I M
  naturality _ _ f := actionAdjoint_naturality I f

/-- The internal-Hom transpose of the action of an ideal power. -/
noncomputable def powerActionAdjoint
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) (n : ℕ) :
    M ⟶
      (ihom (TensorPower.sheaf O
        (I : ringedSiteModuleCategory J O) n)).obj M :=
  MonoidalClosed.curry (powerAction I M n)

/-- Naturality of the adjoint action of an ideal tensor power. -/
theorem powerActionAdjoint_naturality
    (I : Subobject (unitModule J O)) (n : ℕ)
    {M N : ringedSiteModuleCategory J O} (f : M ⟶ N) :
    (𝟭 (ringedSiteModuleCategory J O)).map f ≫ powerActionAdjoint I N n =
      powerActionAdjoint I M n ≫
        (ihom (TensorPower.sheaf O
          (I : ringedSiteModuleCategory J O) n)).map f := sorry

/-- The adjoint ideal-power action as a natural transformation. -/
@[stacks 0GT5 "adjoint ideal-power action natural transformation"]
noncomputable def powerActionAdjointNat
    (I : Subobject (unitModule J O)) (n : ℕ) :
    𝟭 (ringedSiteModuleCategory J O) ⟶
      ihom (TensorPower.sheaf O
        (I : ringedSiteModuleCategory J O) n) where
  app M := powerActionAdjoint I M n
  naturality _ _ f := powerActionAdjoint_naturality I n f

/-- A module sheaf is `I`-torsion free when the adjoint ideal action
`M ⟶ Hom(I, M)` is monomorphic. -/
@[stacks 0GT5 "ideal-torsion-free module"]
abbrev IsTorsionFree
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) : Prop :=
  Mono (actionAdjoint I M)

/-- The subsheaf of `M` annihilated by the `n`th tensor power of `I`, as a bundled subobject
of `M`. -/
@[stacks 0GT5 "torsion subobject for an ideal power"]
noncomputable abbrev powerTorsionSubobject
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) (n : ℕ) : Subobject M :=
  kernelSubobject (powerActionAdjoint I M n)

/-- The inclusion of the bundled `I^n`-torsion subobject into its ambient module. -/
noncomputable abbrev powerTorsionSubobjectι
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) (n : ℕ) :
    (powerTorsionSubobject I M n : ringedSiteModuleCategory J O) ⟶ M :=
  (powerTorsionSubobject I M n).arrow

/-- The functor of sections annihilated by the `n`th tensor power of an ideal sheaf. -/
@[stacks 0GT5 "torsion functor for an ideal power"]
noncomputable def powerTorsionFunctor
    (I : Subobject (unitModule J O)) (n : ℕ) :
    ringedSiteModuleCategory J O ⥤ ringedSiteModuleCategory J O :=
  kernel (powerActionAdjointNat I n)

/-- The subsheaf `M[I^n]` annihilated by the `n`th tensor power of an ideal sheaf. -/
@[stacks 0GT5 "torsion by an ideal power"]
noncomputable abbrev powerTorsion
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) (n : ℕ) :
    ringedSiteModuleCategory J O :=
  (powerTorsionFunctor I n).obj M

/-- The natural inclusion `(-)[I^n] ⟶ 𝟭 Mod(O)`. -/
noncomputable def powerTorsionιNat
    (I : Subobject (unitModule J O)) (n : ℕ) :
    powerTorsionFunctor I n ⟶ 𝟭 _ :=
  kernel.ι (powerActionAdjointNat I n)

/-- The canonical inclusion `M[I^n] ⟶ M`. -/
noncomputable abbrev powerTorsionι
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) (n : ℕ) :
    powerTorsion I M n ⟶ M :=
  (powerTorsionιNat I n).app M

/-- The canonical comparison from the objectwise kernel subobject to the value of the functorial
kernel, obtained because evaluation preserves kernels. -/
@[stacks 0GT5 "bundled and functorial ideal-power torsion"]
noncomputable def powerTorsionSubobjectIso
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) (n : ℕ) :
    (powerTorsionSubobject I M n : ringedSiteModuleCategory J O) ≅
      powerTorsion I M n :=
  kernelSubobjectIso (powerActionAdjoint I M n) ≪≫
    (PreservesKernel.iso
      ((CategoryTheory.evaluation (ringedSiteModuleCategory J O)
        (ringedSiteModuleCategory J O)).obj M)
      (powerActionAdjointNat I n)).symm

/-- The canonical subobject-to-functor comparison intertwines their inclusions into `M`. -/
@[reassoc]
theorem powerTorsionSubobjectIso_hom_comp_ι
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) (n : ℕ) :
    (powerTorsionSubobjectIso I M n).hom ≫ powerTorsionι I M n =
      powerTorsionSubobjectι I M n := sorry

/-- The bundled `I^n`-torsion subobject is bottom exactly when the adjoint `I^n`-action is
monomorphic. -/
@[stacks 0GT5 "vanishing of bundled ideal-power torsion"]
theorem powerTorsionSubobject_eq_bot_iff
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) (n : ℕ) :
    powerTorsionSubobject I M n = ⊥ ↔
      Mono (powerActionAdjoint I M n) := sorry

/-- The functor of sections annihilated by an ideal sheaf; definitionally this is the
first-power torsion functor. -/
@[stacks 0GT5 "torsion functor for an ideal sheaf"]
noncomputable abbrev torsionFunctor
    (I : Subobject (unitModule J O)) :
    ringedSiteModuleCategory J O ⥤ ringedSiteModuleCategory J O :=
  powerTorsionFunctor I 1

/-- The subsheaf `M[I]` annihilated by an ideal sheaf. -/
@[stacks 0GT5 "torsion by an ideal sheaf"]
noncomputable abbrev torsion
  (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) :
    ringedSiteModuleCategory J O :=
  powerTorsion I M 1

/-- The `I`-torsion subsheaf as a bundled subobject of its ambient module. -/
@[stacks 0GT5 "torsion subobject for an ideal sheaf"]
noncomputable abbrev torsionSubobject
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) : Subobject M :=
  powerTorsionSubobject I M 1

/-- The bundled first-power torsion subobject is bottom exactly when `M` is `I`-torsion free. -/
@[stacks 0GT5 "vanishing of bundled ideal torsion"]
theorem torsionSubobject_eq_bot_iff
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) :
    torsionSubobject I M = ⊥ ↔ IsTorsionFree I M := sorry

/-- The natural inclusion `(-)[I] ⟶ 𝟭 Mod(O)`. -/
noncomputable abbrev torsionιNat
    (I : Subobject (unitModule J O)) :
    torsionFunctor I ⟶ 𝟭 _ :=
  powerTorsionιNat I 1

/-- The canonical inclusion `M[I] ⟶ M`. -/
noncomputable abbrev torsionι
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) :
    torsion I M ⟶ M :=
  (torsionιNat I).app M

/-- The functor sending a module sheaf to its quotient by first-power `I`-torsion. -/
@[stacks 0GT5 "quotient by ideal torsion"]
noncomputable def torsionQuotientFunctor
    (I : Subobject (unitModule J O)) :
    ringedSiteModuleCategory J O ⥤ ringedSiteModuleCategory J O :=
  cokernel (torsionιNat I)

/-- The quotient of a module sheaf by its `I`-torsion subsheaf. -/
noncomputable abbrev torsionQuotient
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) :
    ringedSiteModuleCategory J O :=
  (torsionQuotientFunctor I).obj M

/-- The natural quotient map `𝟭 Mod(O) ⟶ (-) / (-)[I]`. -/
noncomputable def torsionQuotientπNat
    (I : Subobject (unitModule J O)) :
    𝟭 _ ⟶ torsionQuotientFunctor I :=
  cokernel.π (torsionιNat I)

/-- The canonical quotient map `M ⟶ M / M[I]`. -/
noncomputable abbrev torsionQuotientπ
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) :
    M ⟶ torsionQuotient I M :=
  (torsionQuotientπNat I).app M

/-- Vanishing of the `I`-torsion subsheaf is equivalent to monicity of the adjoint ideal action. -/
theorem torsion_isZero_iff
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) :
    IsZero (torsion I M) ↔ IsTorsionFree I M := sorry

/-- Vanishing of the `I^n`-torsion object is equivalent to monicity of the adjoint
`I^n`-action. -/
theorem powerTorsion_isZero_iff
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O) (n : ℕ) :
    IsZero (powerTorsion I M n) ↔ Mono (powerActionAdjoint I M n) := sorry

/-- If the ideal object is tensor-invertible, absence of ideal torsion is equivalent to monicity
of the uncurried action `I ⊗ M ⟶ M`. -/
@[stacks 0GT5 "torsion-free versus invertible ideal action"]
theorem isTorsionFree_iff_actionMono
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O)
    [MonoidalCategory.isInvertibleObject
      (I : ringedSiteModuleCategory J O)] :
    IsTorsionFree I M ↔ IsActionMono I M := sorry

/-- If the ideal object is tensor-invertible, absence of first-power torsion is equivalent to
absence of torsion for every positive tensor power. -/
@[stacks 0GT5 "torsion-free versus all positive ideal powers"]
theorem isTorsionFree_iff_forall_powerTorsion
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory J O)
    [MonoidalCategory.isInvertibleObject
      (I : ringedSiteModuleCategory J O)] :
    IsTorsionFree I M ↔
      ∀ n : ℕ+, IsZero (powerTorsion I M n) := sorry

end SheafOfModules.RingedSite.IdealSheaf
