/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import stacks_project.Chap20.«20_2_0_3»
public import ReasLib.Topology.Opens.Instances

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u

namespace CategoryTheory
namespace Sheaf

noncomputable section

/-
Domain-style sampling for 20.2.0.1:
- primary domain: sheaf cohomology of an abelian sheaf on a topological space, computed by global
  sections of an injective resolution;
- sampled owner declarations:
  `CategoryTheory.Sheaf.H'`,
  `CategoryTheory.Sheaf.Γ`,
  `CategoryTheory.Sheaf.ΓNatIsoSheafSections`,
  `CategoryTheory.Sheaf.cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution`;
- best owner abstraction:
  `CategoryTheory.Sheaf.cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution`;
- primitive data: a topological space `X`, an abelian sheaf `F : X.Sheaf AddCommGrpCat`, a chosen
  injective resolution `I : InjectiveResolution F`, and a degree `i : ℕ`;
- derived API: the terminal-open/global-sections specialization, transported along
  `Sheaf.ΓNatIsoSheafSections` from sections over `⊤ : Opens X` to `Sheaf.Γ`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that `H^i(X, F)` is computed by the degree-`i` homology
  of the global-sections complex of an injective resolution of `F`;
- `core/canonical`:
  `CategoryTheory.Sheaf.cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution`;
- `bridge/view`: the terminal-open comparison
  `CategoryTheory.Sheaf.ΓNatIsoSheafSections`, used here to move from objectwise sections at
  `⊤ : Opens X` to `Sheaf.Γ`.

This file therefore stays at the bridge layer: it does not introduce a new owner theorem parallel
to the site-level result from `20_2_0_3`, but it should expose the topological-space/global-sections
specialization as its public entry rather than leaving that specialization only in comments.
-/

variable {X : Type u} [TopologicalSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
-- The owner theorem `cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution`
-- requires `HasInjectiveResolutions` on the abelian-sheaf category. Under pinned Mathlib this is
-- not an available instance for `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat` (there is no
-- active `IsGrothendieckAbelian → EnoughInjectives → HasInjectiveResolutions` chain here), so we
-- take it as a hypothesis exactly as the sibling items `Lemma_20_19_2`, `Lemma_20_22_2`, and
-- `Lemma_21_16_4` do.
variable [HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

local notation "JX" => Opens.grothendieckTopology X
local notation "ΓX" => Sheaf.Γ JX AddCommGrpCat

-- Register `HasWeakSheafify` (immediate from `HasSheafify`) as a local instance so that
-- elaboration of `Sheaf.Γ`/`ΓNatIsoSheafSections` finds `sheafToPresheaf.IsRightAdjoint` directly
-- instead of diverging in typeclass search (module-system synthesis divergence).
local instance instHasWeakSheafifyX : HasWeakSheafify JX AddCommGrpCat.{u} := inferInstance

-- Proof sketch: apply the canonical site-level sections theorem at the terminal object `⊤`, then
-- transport the resulting terminal-open sections complex across `Sheaf.ΓNatIsoSheafSections`.
/-- 20.2.0.1: for a sheaf `F` of abelian groups on a topological space `X`, the cohomology
`H^i(X, F)` is canonically isomorphic to the degree-`i` homology of the global-sections complex of
an injective resolution of `F`. -/
@[stacks 0712]
theorem cohomology_isomorphic_to_homology_globalSections_of_injectiveResolution
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (i : ℕ) :
    IsIsomorphic (F.H' i (⊤ : Opens X))
      ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
        (((ΓX).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  let _ : ∀ U : Opens X, Nonempty (U ⟶ (⊤ : Opens X)) := fun _ ↦ ⟨homOfLE le_top⟩
  let eΓ :
      ΓX ≅ (sheafSections JX AddCommGrpCat.{u}).obj (op (⊤ : Opens X)) :=
    Sheaf.ΓNatIsoSheafSections JX AddCommGrpCat.{u} (Preorder.isTerminalTop (Opens X))
  let eHomology :
      (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
          (((ΓX).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≅
        (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
          ((((sheafSections JX AddCommGrpCat.{u}).obj (op (⊤ : Opens X))).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) :=
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).mapIso
      ((NatIso.mapHomologicalComplex eΓ (ComplexShape.up ℕ)).app I.cocomplex)
  have h :
      IsIsomorphic (F.H' i (⊤ : Opens X))
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
          ((((sheafSections JX AddCommGrpCat.{u}).obj (op (⊤ : Opens X))).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) :=
    ⟨(CohomologyPresheaf.appIso JX F (⊤ : Opens X) i).symm ≪≫
      rightDerivedInclusion_app_obj_iso_homology_sections_complex JX I (⊤ : Opens X) i⟩
  rcases h with
    ⟨e⟩
  exact ⟨e ≪≫ eHomology.symm⟩

end

end Sheaf
end CategoryTheory
