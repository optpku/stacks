/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Descent
import StacksCheckRecall

/-!
@stack 0ALK

# Lemma 15.90.17

Maps whose kernel and cokernel are ideal-power torsion descend through flat
base change when the map is an isomorphism modulo the finitely generated
ideal.  The recalls below retain both orientations of the map and the
canonical kernel and cokernel comparisons attached to a chosen descent.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

namespace LocalizedModule.Away.FormalGluing

variable {R S : Type u} [CommRing R] [CommRing S]

/- Lemma 15.90.17 (0ALK), first orientation: a map into a base-changed
module descends, and its kernel and cokernel are the base changes of those
of the descended map. -/

variable (σ : R →+* S) (I : Ideal R) (hI : I.FG) (hflat : σ.Flat)
variable (hquot : Function.Bijective (σ.quotientByIdeal I))
variable (N : ModuleCat.{u} R) (M' : ModuleCat.{u} S)
variable (α : M' ⟶ (ModuleCat.extendScalars σ).obj N)
variable (hker : Module.IsIdealPowerTorsion
  (Ideal.map σ I) (kernel α : ModuleCat.{u} S))
variable (hcoker : Module.IsIdealPowerTorsion
  (Ideal.map σ I) (cokernel α : ModuleCat.{u} S))

@[stacks 0ALK "Lemma 15.90.17 (1)"]
#check (exists_mapToBaseChangeDescent_of_kernel_cokernel_idealPowerTorsion
    σ I hI hflat hquot N M' α hker hcoker :
  ∃ (M : ModuleCat.{u} R) (ψ : M ⟶ N)
    (e : (ModuleCat.extendScalars σ).obj M ≅ M'),
    CommSq e.hom ((ModuleCat.extendScalars σ).map ψ) α (𝟙 _))

variable {M : ModuleCat.{u} R} (ψ : M ⟶ N)
variable (e : (ModuleCat.extendScalars σ).obj M ≅ M')
variable (hcomm :
  CommSq e.hom ((ModuleCat.extendScalars σ).map ψ) α (𝟙 _))

@[stacks 0ALK "Lemma 15.90.17 (2)"]
#check (mapToBaseChangeKernelIso σ hflat ψ α e hcomm :
  (ModuleCat.extendScalars σ).obj (kernel ψ) ≅ kernel α)

#check (mapToBaseChangeKernelIso_comm σ hflat ψ α e hcomm :
  CommSq ((ModuleCat.extendScalars σ).map (kernel.ι ψ))
    (mapToBaseChangeKernelIso σ hflat ψ α e hcomm).hom
    e.hom (kernel.ι α))

@[stacks 0ALK "Lemma 15.90.17 (3)"]
#check (mapToBaseChangeCokernelIso σ ψ α e hcomm :
  (ModuleCat.extendScalars σ).obj (cokernel ψ) ≅ cokernel α)

#check (mapToBaseChangeCokernelIso_comm σ ψ α e hcomm :
  CommSq ((ModuleCat.extendScalars σ).map (cokernel.π ψ)) (𝟙 _)
    (mapToBaseChangeCokernelIso σ ψ α e hcomm).hom (cokernel.π α))

/- Lemma 15.90.17 (0ALK), second orientation: a map out of a base-changed
module descends, with the analogous kernel and cokernel comparisons. -/

variable (N' : ModuleCat.{u} S)
variable (β : (ModuleCat.extendScalars σ).obj M ⟶ N')
variable (hker' : Module.IsIdealPowerTorsion
  (Ideal.map σ I) (kernel β : ModuleCat.{u} S))
variable (hcoker' : Module.IsIdealPowerTorsion
  (Ideal.map σ I) (cokernel β : ModuleCat.{u} S))

@[stacks 0ALK "Lemma 15.90.17 (4)"]
#check (exists_mapFromBaseChangeDescent_of_kernel_cokernel_idealPowerTorsion
    σ I hI hflat hquot M N' β hker' hcoker' :
  ∃ (N : ModuleCat.{u} R) (ψ : M ⟶ N)
    (e : (ModuleCat.extendScalars σ).obj N ≅ N'),
    CommSq ((ModuleCat.extendScalars σ).map ψ) β e.hom (𝟙 _))

variable {N₀ : ModuleCat.{u} R} (ψ' : M ⟶ N₀)
variable (e' : (ModuleCat.extendScalars σ).obj N₀ ≅ N')
variable (hcomm' :
  CommSq ((ModuleCat.extendScalars σ).map ψ') β e'.hom (𝟙 _))

@[stacks 0ALK "Lemma 15.90.17 (5)"]
#check (mapFromBaseChangeKernelIso σ hflat ψ' β e' hcomm' :
  (ModuleCat.extendScalars σ).obj (kernel ψ') ≅ kernel β)

#check (mapFromBaseChangeKernelIso_comm σ hflat ψ' β e' hcomm' :
  CommSq ((ModuleCat.extendScalars σ).map (kernel.ι ψ'))
    (mapFromBaseChangeKernelIso σ hflat ψ' β e' hcomm').hom
    (𝟙 _) (kernel.ι β))

@[stacks 0ALK "Lemma 15.90.17 (6)"]
#check (mapFromBaseChangeCokernelIso σ ψ' β e' hcomm' :
  (ModuleCat.extendScalars σ).obj (cokernel ψ') ≅ cokernel β)

#check (mapFromBaseChangeCokernelIso_comm σ ψ' β e' hcomm' :
  CommSq ((ModuleCat.extendScalars σ).map (cokernel.π ψ')) e'.hom
    (mapFromBaseChangeCokernelIso σ ψ' β e' hcomm').hom (cokernel.π β))

end LocalizedModule.Away.FormalGluing
