/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Torsion
public import ReasLib.Algebra.Module.IdealPower.Torsion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.RegularPrincipal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.SectionAction.Regular
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.InternalHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Torsion and regularity for locally principal ideal sheaves

This file is the ringed-space specialization of ideal-power torsion.  It identifies the generic
tensor-power kernel with the usual stalkwise ideal-power annihilator, then relates torsion
freeness to multiplication by local generators of a locally principal regular ideal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open SheafOfModules.RingedSite.IdealSheaf
open scoped ModuleRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf

variable {X : RingedSpace.{u}}

namespace Chart

/-- A principal-chart generator acts monomorphically on a restricted module exactly when all of
its germs act regularly on the corresponding stalk modules. -/
@[stacks 0GT5 "principal-chart action regularity"]
theorem action_mono_iff
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X} (c : Chart I U) (M : X.Modules) :
    Mono (c.action M) ↔
      ∀ (x : X) (hx : x ∈ U),
        IsSMulRegular (stalkModuleCat M x)
          (X.presheaf.germ U x hx c.generator) := sorry

end Chart

/-- On every principal chart for `I`, the chart generator acts monomorphically on the
restricted module sheaf. -/
@[stacks 0GT5 "regular action on principal charts"]
def ActsMonoLocally
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) : Prop :=
  ∀ (U : Opens X) (c : Chart I U), Mono (c.action M)

/-- Every generator of the stalk ideal of `I` acts regularly on the stalk of `M`. -/
@[stacks 0GT5 "regular action of stalk-ideal generators"]
def IsRegularOn
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) : Prop :=
  ∀ (x : X) (f : X.presheaf.stalk x),
    idealSheafStalkIdeal I x = Ideal.span {f} →
      IsSMulRegular (stalkModuleCat M x) f

namespace PowerTorsion

/-- The submodule of the stalk of `M` annihilated by the `n`th power of the stalk ideal of
`I`. -/
@[stacks 0GT5 "stalk ideal-power torsion submodule"]
noncomputable abbrev stalkSubmodule
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ) (x : X) :
    Submodule (X.presheaf.stalk x) (stalkModuleCat (X := X) M x) :=
  (idealSheafStalkIdeal I x).powerAnnihilatedSubmodule
    (stalkModuleCat (X := X) M x) n

/-- The stalk ideal-power torsion submodule, bundled as a module over the structure-sheaf
stalk. -/
@[stacks 0GT5 "bundled stalk ideal-power torsion"]
noncomputable abbrev stalkModule
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ) (x : X) :
    ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of.{u, u} (X.presheaf.stalk x)
    (stalkSubmodule I M n x)

/-- The canonical inclusion of the stalk ideal-power torsion module into the ambient stalk
module. -/
@[stacks 0GT5 "stalk ideal-power torsion inclusion"]
noncomputable def stalkι
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ) (x : X) :
    stalkModule I M n x ⟶ stalkModuleCat (X := X) M x :=
  @ModuleCat.ofHom (X.presheaf.stalk x) inferInstance
    (stalkSubmodule I M n x) (stalkModuleCat (X := X) M x)
    inferInstance inferInstance inferInstance (moduleStalkModule (X := X) M x)
    (stalkSubmodule I M n x).subtype

/-- The linear map on stalks induced by the inclusion of the `I^n`-torsion subsheaf. -/
@[stacks 0GT5 "stalk map of the ideal-power torsion inclusion"]
noncomputable def stalkMap
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ) (x : X) :
    stalkModuleCat (X := X)
        (SheafOfModules.RingedSite.IdealSheaf.powerTorsion
          (O := X.sheaf) I M n) x
      →ₗ[X.presheaf.stalk x] stalkModuleCat (X := X) M x :=
  (moduleStalkHom (X := X) x
    (SheafOfModules.RingedSite.IdealSheaf.powerTorsionι
      (O := X.sheaf) I M n)).hom

/-- The stalk of the inclusion of the `I^n`-torsion subsheaf lands in the submodule annihilated
by the `n`th power of the stalk ideal. -/
theorem stalkMap_mem
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ)
    (x : X)
    (m : stalkModuleCat (X := X)
      (SheafOfModules.RingedSite.IdealSheaf.powerTorsion
        (O := X.sheaf) I M n) x) :
    stalkMap I M n x m ∈ stalkSubmodule I M n x := sorry

/-- The canonical comparison from the stalk of the `I^n`-torsion subsheaf to the usual
stalk-module submodule annihilated by the `n`th power of the stalk ideal. -/
@[stacks 0GT5 "stalk comparison for ideal-power torsion"]
noncomputable def stalkComparison
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ) (x : X) :
    stalkModuleCat (X := X)
        (SheafOfModules.RingedSite.IdealSheaf.powerTorsion
          (O := X.sheaf) I M n) x ⟶
      stalkModule I M n x :=
  @ModuleCat.ofHom (X.presheaf.stalk x) inferInstance
    (stalkModuleCat (X := X)
      (SheafOfModules.RingedSite.IdealSheaf.powerTorsion
        (O := X.sheaf) I M n) x)
    (stalkSubmodule I M n x)
    inferInstance
    (moduleStalkModule (X := X)
      (SheafOfModules.RingedSite.IdealSheaf.powerTorsion
        (O := X.sheaf) I M n) x)
    inferInstance inferInstance
    ((stalkMap I M n x).codRestrict
      (stalkSubmodule I M n x) (stalkMap_mem I M n x))

/-- The stalk comparison followed by the annihilator-submodule inclusion is the stalk of the
torsion-subsheaf inclusion. -/
@[reassoc]
theorem stalkComparison_comp_ι
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ) (x : X) :
    stalkComparison I M n x ≫ stalkι I M n x =
      moduleStalkHom (X := X) x
        (SheafOfModules.RingedSite.IdealSheaf.powerTorsionι
          (O := X.sheaf) I M n) := sorry

/-- Finite presentation of the ideal tensor power makes the canonical stalk comparison for
`I^n`-torsion an isomorphism. -/
@[stacks 0GT5 "stalk description of ideal-power torsion", instance]
instance stalkComparison_isIso
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ)
    [(SheafOfModules.RingedSite.TensorPower.sheaf
      X.sheaf (I : X.Modules) n).IsFinitePresentation]
    (x : X) :
    IsIso (stalkComparison I M n x) := sorry

/-- If the relevant tensor power of an ideal sheaf is finitely presented, the stalk of its
torsion subsheaf is canonically isomorphic to the usual annihilated submodule. -/
@[stacks 0GT5 "stalk description of ideal-power torsion"]
noncomputable def stalkIso
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ)
    [(SheafOfModules.RingedSite.TensorPower.sheaf
      X.sheaf (I : X.Modules) n).IsFinitePresentation]
    (x : X) :
    stalkModuleCat (X := X)
        (SheafOfModules.RingedSite.IdealSheaf.powerTorsion
          (O := X.sheaf) I M n) x ≅
      stalkModule I M n x :=
  asIso (stalkComparison I M n x)

/-- The canonical stalk-torsion isomorphism is compatible with the inclusions into the ambient
stalk module. -/
@[reassoc]
theorem stalkIso_hom_comp_ι
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ)
    [(SheafOfModules.RingedSite.TensorPower.sheaf
      X.sheaf (I : X.Modules) n).IsFinitePresentation]
    (x : X) :
    (stalkIso I M n x).hom ≫ stalkι I M n x =
      moduleStalkHom (X := X) x
        (SheafOfModules.RingedSite.IdealSheaf.powerTorsionι
          (O := X.sheaf) I M n) := sorry

/-- If the relevant tensor power of an ideal sheaf is finitely presented, vanishing of its
torsion subsheaf is detected by the usual annihilated submodules on all stalks. -/
@[stacks 0GT5 "stalkwise vanishing of ideal-power torsion"]
theorem isZero_iff_stalk
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (n : ℕ)
    [(SheafOfModules.RingedSite.TensorPower.sheaf
      X.sheaf (I : X.Modules) n).IsFinitePresentation] :
    IsZero (SheafOfModules.RingedSite.IdealSheaf.powerTorsion
      (O := X.sheaf) I M n) ↔
      ∀ x : X, stalkSubmodule I M n x = ⊥ := sorry

end PowerTorsion

namespace IsRegularPrincipal

/-- For a locally principal regular ideal, the global ideal action is monomorphic exactly when
the generator action is monomorphic on every principal chart. -/
@[stacks 0GT5 "global versus chartwise ideal action"]
theorem actionMono_iff_actsMonoLocally
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) [IsRegularPrincipal I] :
    IsActionMono I M ↔ ActsMonoLocally I M := sorry

/-- Monicity of all principal-chart actions is equivalent to regularity of every generator of
the corresponding stalk ideals. -/
@[stacks 0GT5 "chartwise versus stalkwise regularity"]
theorem actsMonoLocally_iff_isRegularOn
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) [IsRegularPrincipal I] :
    ActsMonoLocally I M ↔ IsRegularOn I M := sorry

/-- Lemma 20.55.3 (0GT5): for a locally principal regular ideal sheaf, vanishing of first and
all positive ideal-power torsion, monicity of the ideal action, local generator injectivity,
and stalkwise regularity of ideal generators are equivalent. -/
@[stacks 0GT5]
theorem torsion_tfae
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) [IsRegularPrincipal I] :
    ([ IsZero (SheafOfModules.RingedSite.IdealSheaf.torsion
         (O := X.sheaf) I M),
       ∀ n : ℕ+, IsZero
         (SheafOfModules.RingedSite.IdealSheaf.powerTorsion
           (O := X.sheaf) I M (n : ℕ)),
       IsActionMono I M,
       ActsMonoLocally I M,
       IsRegularOn I M ] : List Prop).TFAE := sorry

end IsRegularPrincipal

end AlgebraicGeometry.RingedSpace.IdealSheaf
