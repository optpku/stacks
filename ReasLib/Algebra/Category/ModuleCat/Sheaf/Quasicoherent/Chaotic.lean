/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sections.Chaotic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasicoherent module sheaves on a chaotic site

On the chaotic topology, Mathlib's local-presentation predicate for quasicoherence agrees with
the reusable base-change compatibility property of the underlying module presheaf.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.IsQuasicoherent

variable {C : Type u} [Category.{v} C]
variable (O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ U : C, HasWeakSheafify
  ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat.{w}]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective
  AddCommGrpCat.{w}]

/-- Lemma 18.24.3 (0GZN): on a chaotic site, a module sheaf is quasicoherent exactly when its
underlying module presheaf is compatible with base change on sections. -/
@[stacks 0GZN]
theorem iff_baseChangeCompatible
    (M : ringedSiteModuleCategory.{u, v, w, w}
      (⊥ : GrothendieckTopology C) O) :
    M.IsQuasicoherent ↔ BaseChange.compatible O M := sorry

/-- The base-change criterion for quasicoherence, expanded as an isomorphism condition on every
canonical comparison map. -/
theorem iff_isIso_map
    (M : ringedSiteModuleCategory.{u, v, w, w}
      (⊥ : GrothendieckTopology C) O) :
    M.IsQuasicoherent ↔
      ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso (BaseChange.map O M f) := sorry

end SheafOfModules.IsQuasicoherent
