/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap96.Definition_96_12_1_LocallyQuasicoherent
public import stacks_project.Chap96.«96_10_3_3_Restriction»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 96.14.1

If a category fibred in groupoids over `(Sch/S)_fppf` is represented by an
algebraic space `F`, restriction of locally quasi-coherent étale modules along
`restrictModules` (the module form of 96.10.2.1) lands in quasi-coherent
modules on `F_étale`.

`restrictModules` lives on the ring-valued étale ringed site of Lemma 96.10.1,
which cannot be imported together with `etaleModules` / `IsLocallyQuasiCoherent`.
Local quasi-coherence is therefore the Definition 96.12.1 class, after
identifying the underlying ring presheaf of `𝒪_X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}

/-- The étale and fppf presentations of `𝒪_X` have the same underlying ring
presheaf on the total category of `X`. -/
theorem etaleStructureSheaf_obj_eq (X : GroupoidsOver S) :
    (etaleRingedSite X).structureSheaf.obj = (structureSheaf X).obj :=
  sorry

/-- Local quasi-coherence of an étale `𝒪_X`-module sheaf, as the
Definition 96.12.1 class on the underlying fppf module presheaf. -/
abbrev IsLocallyQuasicoherentEtale
    (ℱ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) : Prop :=
  IsLocallyQuasicoherent (etaleStructureSheaf_obj_eq X ▸ ℱ.val)

/-- Lemma 96.14.1: let `S` be a scheme, and let `X → (Sch/S)_fppf` be a category
fibred in groupoids represented by an algebraic space `F` via
`e : F.toGroupoids ≌ X`. If `ℱ` is in `LQCoh(𝒪_X)`, then the restriction
`ℱ|_{F_étale}` of 96.10.2.1, identified with `(restrictModules e).obj ℱ` as
`π_{F,*} ℱ = i_F⁻¹ ℱ`, is a quasi-coherent sheaf on `(F_étale, 𝒪_F)`. -/
@[stacks 0GQC]
instance restrictModules_isQuasicoherent (e : F.toGroupoids ≌ X)
    (ℱ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf)
    [IsLocallyQuasicoherentEtale ℱ] :
    ((restrictModules e).obj ℱ).IsQuasicoherent :=
  sorry

/-- Locally quasi-coherent étale modules restrict along `restrictModules e` to
quasi-coherent modules on the representing algebraic space. -/
theorem restrictModules_le (e : F.toGroupoids ≌ X) :
    IsLocallyQuasicoherentEtale ≤
      (AlgebraicSpace.quasiCoherentModuleProperty F).inverseImage (restrictModules e) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
