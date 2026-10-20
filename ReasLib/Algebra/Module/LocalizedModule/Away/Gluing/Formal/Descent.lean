/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Equivalence
public import ReasLib.Algebra.Category.ModuleCat.IdealPower.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent of module maps through formal gluing

Under the formal-gluing hypotheses, a map with ideal-power-torsion kernel
and cokernel descends across extension of scalars.  The two possible
orientations are kept separate.  Once a descended map and its comparison
isomorphism are fixed, the kernel and cokernel comparisons are canonical:
they come from preservation of kernels by flat base change, preservation of
cokernels by extension of scalars, and transport across the comparison
square.

@stack 0ALK
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

namespace LocalizedModule.Away.FormalGluing

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Lemma 15.90.17 (1): a map from an `S`-module to a base-changed
`R`-module descends when its kernel and cokernel are power torsion. -/
@[stacks 0ALK "descent of a map into a base-changed module"]
theorem exists_mapToBaseChangeDescent_of_kernel_cokernel_idealPowerTorsion
    (σ : R →+* S) (I : Ideal R) (hI : I.FG) (hflat : σ.Flat)
    (hquot : Function.Bijective (σ.quotientByIdeal I))
    (N : ModuleCat.{u} R) (M' : ModuleCat.{u} S)
    (α : M' ⟶ (ModuleCat.extendScalars σ).obj N)
    (hker : Module.IsIdealPowerTorsion
      (Ideal.map σ I) (kernel α : ModuleCat.{u} S))
    (hcoker : Module.IsIdealPowerTorsion
      (Ideal.map σ I) (cokernel α : ModuleCat.{u} S)) :
    ∃ (M : ModuleCat.{u} R) (ψ : M ⟶ N)
      (e : (ModuleCat.extendScalars σ).obj M ≅ M'),
      CommSq e.hom ((ModuleCat.extendScalars σ).map ψ) α (𝟙 _) := sorry

/-- Normalize the comparison square for a map into a base-changed module
to the orientation used by `kernel.mapIso` and `cokernel.mapIso`. -/
@[stacks 0ALK "map-to-base-change comparison equation"]
theorem mapToBaseChange_square_eq
    (σ : R →+* S) {M N : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (ψ : M ⟶ N) (α : M' ⟶ (ModuleCat.extendScalars σ).obj N)
    (e : (ModuleCat.extendScalars σ).obj M ≅ M')
    (hcomm : CommSq e.hom ((ModuleCat.extendScalars σ).map ψ) α (𝟙 _)) :
    (ModuleCat.extendScalars σ).map ψ ≫ (Iso.refl _).hom =
      e.hom ≫ α := sorry

/-- Flat base change identifies the base change of the descended kernel
with the kernel of the original map into a base-changed module. -/
@[stacks 0ALK "kernel comparison for a map into a base-changed module"]
noncomputable def mapToBaseChangeKernelIso
    (σ : R →+* S) (hflat : σ.Flat)
    {M N : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (ψ : M ⟶ N) (α : M' ⟶ (ModuleCat.extendScalars σ).obj N)
    (e : (ModuleCat.extendScalars σ).obj M ≅ M')
    (hcomm : CommSq e.hom ((ModuleCat.extendScalars σ).map ψ) α (𝟙 _)) :
    (ModuleCat.extendScalars σ).obj (kernel ψ) ≅ kernel α :=
  letI : PreservesLimitsOfShape WalkingParallelPair
      (ModuleCat.extendScalars.{u, u, u} σ) :=
    (ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat).preservesFiniteLimits
      WalkingParallelPair
  PreservesKernel.iso (ModuleCat.extendScalars.{u, u, u} σ) ψ ≪≫
    kernel.mapIso ((ModuleCat.extendScalars σ).map ψ) α e (Iso.refl _)
      (mapToBaseChange_square_eq σ ψ α e hcomm)

/-- The kernel comparison commutes with the two kernel inclusions and the
chosen descent isomorphism. -/
@[stacks 0ALK "kernel comparison square for a map into a base-changed module"]
theorem mapToBaseChangeKernelIso_comm
    (σ : R →+* S) (hflat : σ.Flat)
    {M N : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (ψ : M ⟶ N) (α : M' ⟶ (ModuleCat.extendScalars σ).obj N)
    (e : (ModuleCat.extendScalars σ).obj M ≅ M')
    (hcomm : CommSq e.hom ((ModuleCat.extendScalars σ).map ψ) α (𝟙 _)) :
    CommSq ((ModuleCat.extendScalars σ).map (kernel.ι ψ))
      (mapToBaseChangeKernelIso σ hflat ψ α e hcomm).hom
      e.hom (kernel.ι α) := sorry

/-- Extension of scalars identifies the base change of the descended
cokernel with the cokernel of the original map into a base-changed module. -/
@[stacks 0ALK "cokernel comparison for a map into a base-changed module"]
noncomputable def mapToBaseChangeCokernelIso
    (σ : R →+* S) {M N : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (ψ : M ⟶ N) (α : M' ⟶ (ModuleCat.extendScalars σ).obj N)
    (e : (ModuleCat.extendScalars σ).obj M ≅ M')
    (hcomm : CommSq e.hom ((ModuleCat.extendScalars σ).map ψ) α (𝟙 _)) :
    (ModuleCat.extendScalars σ).obj (cokernel ψ) ≅ cokernel α :=
  letI : PreservesColimitsOfShape WalkingParallelPair
      (ModuleCat.extendScalars.{u, u, u} σ) :=
    (ModuleCat.extendRestrictScalarsAdj σ).leftAdjoint_preservesColimits.preservesColimitsOfShape
  PreservesCokernel.iso (ModuleCat.extendScalars.{u, u, u} σ) ψ ≪≫
    cokernel.mapIso ((ModuleCat.extendScalars σ).map ψ) α e (Iso.refl _)
      (mapToBaseChange_square_eq σ ψ α e hcomm)

/-- The cokernel comparison commutes with the two cokernel projections. -/
@[stacks 0ALK "cokernel comparison square for a map into a base-changed module"]
theorem mapToBaseChangeCokernelIso_comm
    (σ : R →+* S) {M N : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (ψ : M ⟶ N) (α : M' ⟶ (ModuleCat.extendScalars σ).obj N)
    (e : (ModuleCat.extendScalars σ).obj M ≅ M')
    (hcomm : CommSq e.hom ((ModuleCat.extendScalars σ).map ψ) α (𝟙 _)) :
    CommSq ((ModuleCat.extendScalars σ).map (cokernel.π ψ)) (𝟙 _)
      (mapToBaseChangeCokernelIso σ ψ α e hcomm).hom (cokernel.π α) := sorry

/-- Lemma 15.90.17 (2): a map from a base-changed `R`-module to an
`S`-module descends when its kernel and cokernel are power torsion. -/
@[stacks 0ALK "descent of a map from a base-changed module"]
theorem exists_mapFromBaseChangeDescent_of_kernel_cokernel_idealPowerTorsion
    (σ : R →+* S) (I : Ideal R) (hI : I.FG) (hflat : σ.Flat)
    (hquot : Function.Bijective (σ.quotientByIdeal I))
    (M : ModuleCat.{u} R) (N' : ModuleCat.{u} S)
    (α : (ModuleCat.extendScalars σ).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion
      (Ideal.map σ I) (kernel α : ModuleCat.{u} S))
    (hcoker : Module.IsIdealPowerTorsion
      (Ideal.map σ I) (cokernel α : ModuleCat.{u} S)) :
    ∃ (N : ModuleCat.{u} R) (ψ : M ⟶ N)
      (e : (ModuleCat.extendScalars σ).obj N ≅ N'),
      CommSq ((ModuleCat.extendScalars σ).map ψ) α e.hom (𝟙 _) := sorry

/-- Normalize the comparison square for a map from a base-changed module
to the orientation used by `kernel.mapIso` and `cokernel.mapIso`. -/
@[stacks 0ALK "map-from-base-change comparison equation"]
theorem mapFromBaseChange_square_eq
    (σ : R →+* S) {M N : ModuleCat.{u} R} {N' : ModuleCat.{u} S}
    (ψ : M ⟶ N) (α : (ModuleCat.extendScalars σ).obj M ⟶ N')
    (e : (ModuleCat.extendScalars σ).obj N ≅ N')
    (hcomm : CommSq ((ModuleCat.extendScalars σ).map ψ) α e.hom (𝟙 _)) :
    (ModuleCat.extendScalars σ).map ψ ≫ e.hom =
      (Iso.refl _).hom ≫ α := sorry

/-- Flat base change identifies the base change of the descended kernel
with the kernel of the original map from a base-changed module. -/
@[stacks 0ALK "kernel comparison for a map from a base-changed module"]
noncomputable def mapFromBaseChangeKernelIso
    (σ : R →+* S) (hflat : σ.Flat)
    {M N : ModuleCat.{u} R} {N' : ModuleCat.{u} S}
    (ψ : M ⟶ N) (α : (ModuleCat.extendScalars σ).obj M ⟶ N')
    (e : (ModuleCat.extendScalars σ).obj N ≅ N')
    (hcomm : CommSq ((ModuleCat.extendScalars σ).map ψ) α e.hom (𝟙 _)) :
    (ModuleCat.extendScalars σ).obj (kernel ψ) ≅ kernel α :=
  letI : PreservesLimitsOfShape WalkingParallelPair
      (ModuleCat.extendScalars.{u, u, u} σ) :=
    (ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat).preservesFiniteLimits
      WalkingParallelPair
  PreservesKernel.iso (ModuleCat.extendScalars.{u, u, u} σ) ψ ≪≫
    kernel.mapIso ((ModuleCat.extendScalars σ).map ψ) α (Iso.refl _) e
      (mapFromBaseChange_square_eq σ ψ α e hcomm)

/-- The kernel comparison commutes with the two kernel inclusions. -/
@[stacks 0ALK "kernel comparison square for a map from a base-changed module"]
theorem mapFromBaseChangeKernelIso_comm
    (σ : R →+* S) (hflat : σ.Flat)
    {M N : ModuleCat.{u} R} {N' : ModuleCat.{u} S}
    (ψ : M ⟶ N) (α : (ModuleCat.extendScalars σ).obj M ⟶ N')
    (e : (ModuleCat.extendScalars σ).obj N ≅ N')
    (hcomm : CommSq ((ModuleCat.extendScalars σ).map ψ) α e.hom (𝟙 _)) :
    CommSq ((ModuleCat.extendScalars σ).map (kernel.ι ψ))
      (mapFromBaseChangeKernelIso σ hflat ψ α e hcomm).hom
      (𝟙 _) (kernel.ι α) := sorry

/-- Extension of scalars identifies the base change of the descended
cokernel with the cokernel of the original map from a base-changed module. -/
@[stacks 0ALK "cokernel comparison for a map from a base-changed module"]
noncomputable def mapFromBaseChangeCokernelIso
    (σ : R →+* S) {M N : ModuleCat.{u} R} {N' : ModuleCat.{u} S}
    (ψ : M ⟶ N) (α : (ModuleCat.extendScalars σ).obj M ⟶ N')
    (e : (ModuleCat.extendScalars σ).obj N ≅ N')
    (hcomm : CommSq ((ModuleCat.extendScalars σ).map ψ) α e.hom (𝟙 _)) :
    (ModuleCat.extendScalars σ).obj (cokernel ψ) ≅ cokernel α :=
  letI : PreservesColimitsOfShape WalkingParallelPair
      (ModuleCat.extendScalars.{u, u, u} σ) :=
    (ModuleCat.extendRestrictScalarsAdj σ).leftAdjoint_preservesColimits.preservesColimitsOfShape
  PreservesCokernel.iso (ModuleCat.extendScalars.{u, u, u} σ) ψ ≪≫
    cokernel.mapIso ((ModuleCat.extendScalars σ).map ψ) α (Iso.refl _) e
      (mapFromBaseChange_square_eq σ ψ α e hcomm)

/-- The cokernel comparison commutes with the two cokernel projections and
the chosen descent isomorphism. -/
@[stacks 0ALK "cokernel comparison square for a map from a base-changed module"]
theorem mapFromBaseChangeCokernelIso_comm
    (σ : R →+* S) {M N : ModuleCat.{u} R} {N' : ModuleCat.{u} S}
    (ψ : M ⟶ N) (α : (ModuleCat.extendScalars σ).obj M ⟶ N')
    (e : (ModuleCat.extendScalars σ).obj N ≅ N')
    (hcomm : CommSq ((ModuleCat.extendScalars σ).map ψ) α e.hom (𝟙 _)) :
    CommSq ((ModuleCat.extendScalars σ).map (cokernel.π ψ)) e.hom
      (mapFromBaseChangeCokernelIso σ ψ α e hcomm).hom (cokernel.π α) := sorry

end LocalizedModule.Away.FormalGluing
