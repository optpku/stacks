/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Topology.LocallyFinite
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support
public import ReasLib.CategoryTheory.Functor.SectionsTerminal
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import ReasLib.Topology.Sheaves.Glue
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally finite sections of coproducts of sheaves of modules

A section of an infinite coproduct need not be a globally finite sum.  A locally finite family of
component sections does, however, determine a section: on every sufficiently small open set only
finitely many components remain, and these finite sums glue.  This file provides that construction
and its specialization to morphisms between free sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open scoped BigOperators

noncomputable section

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {𝒪 : X.Sheaf RingCat.{u}}

namespace SectionFamily

variable {ι : Type u} (M : ι → SheafOfModules.{u} 𝒪) (s : ∀ i, (M i).sections)
variable [HasCoproduct M]

/-- Opens meeting the supports of only finitely many sections in a family. -/
def FiniteOpen :=
  {U : Opens X // {i | (sectionSupport (s i) ∩ (U : Set X)).Nonempty}.Finite}

namespace FiniteOpen

/-- The open subset underlying a finite-support open. -/
abbrev toOpens (U : FiniteOpen M s) : Opens X := U.1

/-- The canonical inclusion of a finite-support open into the whole space. -/
def toTop (U : FiniteOpen M s) : U.toOpens ⟶ (⊤ : Opens X) :=
  homOfLE le_top

/-- The finite set of components whose support meets a finite-support open. -/
noncomputable def active (U : FiniteOpen M s) : Finset ι :=
  U.2.toFinset

/-- A component is active exactly when its support meets the open. -/
@[simp]
theorem mem_active_iff (U : FiniteOpen M s) (i : ι) :
    i ∈ U.active ↔ (sectionSupport (s i) ∩ (U.toOpens : Set X)).Nonempty := by
  exact Set.Finite.mem_toFinset U.2

end FiniteOpen

/-- A locally finite family of supports is covered by its finite-support opens. -/
theorem finiteOpen_cover
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) :
    (⊤ : Opens X) ≤ ⨆ U : FiniteOpen M s, U.toOpens := by
  intro x _
  obtain ⟨V, hV, hfin⟩ := hs x
  obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp hV
  have hfinU : {i | (sectionSupport (s i) ∩ U).Nonempty}.Finite :=
    hfin.subset fun i hi ↦ hi.mono (Set.inter_subset_inter_right _ hUV)
  exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hfinU⟩, hxU⟩

/-- The finite sum of the component sections on a finite-support open. -/
noncomputable def localSum (U : FiniteOpen M s) :
    ((∐ M).val.obj (op U.toOpens)) :=
  ∑ i ∈ U.active, (sectionsMap (Sigma.ι M i) (s i)).val (op U.toOpens)

private theorem component_eval_eq_zero (i : ι) (U : Opens X)
    (h : ¬ (sectionSupport (s i) ∩ (U : Set X)).Nonempty) :
    (s i).val (op U) = 0 := by
  apply TopCat.Presheaf.section_ext ((toSheaf 𝒪).obj (M i)) U
  intro x hx
  have hg : TopCat.Presheaf.Γgerm (M i).val.presheaf x ((s i).val (op ⊤)) = 0 := by
    by_contra hn
    exact h ⟨x, hn, hx⟩
  change TopCat.Presheaf.germ (M i).val.presheaf U x hx ((s i).val (op U)) =
    TopCat.Presheaf.germ (M i).val.presheaf U x hx 0
  rw [map_zero]
  calc
    TopCat.Presheaf.germ (M i).val.presheaf U x hx ((s i).val (op U)) =
        TopCat.Presheaf.germ (M i).val.presheaf U x hx
          ((M i).val.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            ((s i).val (op ⊤))) := by
      exact congrArg (fun z ↦ TopCat.Presheaf.germ (M i).val.presheaf U x hx z)
        ((s i).property (homOfLE (le_top : U ≤ ⊤)).op).symm
    _ = TopCat.Presheaf.Γgerm (M i).val.presheaf x ((s i).val (op ⊤)) :=
      TopCat.Presheaf.Γgerm_res_apply (M i).val.presheaf x hx _
    _ = 0 := hg

/-- The local finite sums agree on overlaps. -/
theorem localSum_compatible :
    TopCat.Presheaf.IsCompatible ((toSheaf 𝒪).obj (∐ M)).obj
      (fun U : FiniteOpen M s ↦ U.toOpens) (localSum M s) := by
  classical
  intro U V
  change (∐ M).val.map (Opens.infLELeft U.toOpens V.toOpens).op (localSum M s U) =
    (∐ M).val.map (Opens.infLERight U.toOpens V.toOpens).op (localSum M s V)
  simp only [localSum, map_sum, PresheafOfModules.sections_property]
  apply Finset.sum_congr_of_eq_on_inter
  · intro i _ hiV
    have hz := component_eval_eq_zero M s i (U.toOpens ⊓ V.toOpens) (by
      rintro ⟨x, hx, hxUV⟩
      exact hiV ((FiniteOpen.mem_active_iff M s V i).mpr ⟨x, hx, hxUV.2⟩))
    change (Sigma.ι M i).val.app _ ((s i).val _) = 0
    rw [hz]
    exact map_zero _
  · intro i _ hiU
    have hz := component_eval_eq_zero M s i (U.toOpens ⊓ V.toOpens) (by
      rintro ⟨x, hx, hxUV⟩
      exact hiU ((FiniteOpen.mem_active_iff M s U i).mpr ⟨x, hx, hxUV.1⟩))
    change (Sigma.ι M i).val.app _ ((s i).val _) = 0
    rw [hz]
    exact map_zero _
  · intro i _ _
    rfl

/-- The value on the whole space obtained by gluing the local finite sums. -/
noncomputable def gluedTopSection
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) :
    ((∐ M).val.obj (op (⊤ : Opens X))) :=
  TopCat.Sheaf.glueOfCompatibleFamily
    ((toSheaf 𝒪).obj (∐ M) : X.Sheaf AddCommGrpCat.{u})
    (fun U : FiniteOpen M s ↦ U.toOpens) ⊤ (fun U ↦ U.toTop)
    (finiteOpen_cover M s hs) (localSum M s) (localSum_compatible M s)

/-- A locally finite family of component sections determines a section of their coproduct. -/
@[stacks 01BL "locally finite coproduct section"]
noncomputable def toCoproduct
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) :
    (∐ M).sections :=
  (CategoryTheory.Functor.sectionsEquivTerminal
    ((∐ M).val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) ⊤ isTerminalTop).symm
      (gluedTopSection M s hs)

/-- On a finite-support open, the locally finite coproduct section is the expected finite sum. -/
theorem toCoproduct_eval_finiteOpen
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) (U : FiniteOpen M s) :
    (toCoproduct M s hs).val (op U.toOpens) = localSum M s U := by
  let F := ((toSheaf 𝒪).obj (∐ M) : X.Sheaf AddCommGrpCat.{u})
  let P := F.obj ⋙ CategoryTheory.forget AddCommGrpCat
  let hP : TopCat.Presheaf.IsSheaf P :=
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (CategoryTheory.forget AddCommGrpCat)
      F.obj).mp F.property
  let t := (hP.isSheafPairwiseIntersections
    (fun U : FiniteOpen M s ↦ U.toOpens)).some
  let c := TopCat.Presheaf.IsCompatible.sectionPairwise (F := P) (localSum_compatible M s)
  change P.map U.toTop.op
    (P.map (eqToHom (le_antisymm (finiteOpen_cover M s hs)
      (iSup_le fun U : FiniteOpen M s ↦ U.toTop.le))).op
      (t.lift (Types.coneOfSection c.property) PUnit.unit)) = localSum M s U
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  exact ConcreteCategory.congr_hom
    (t.fac (Types.coneOfSection c.property) (op (Pairwise.single U))) PUnit.unit

/-- On any open with a specified finite set of active components, the locally finite coproduct
section is the corresponding finite sum. -/
theorem toCoproduct_eval
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) (U : Opens X) (t : Finset ι)
    (ht : ∀ i, (sectionSupport (s i) ∩ (U : Set X)).Nonempty → i ∈ t) :
    (toCoproduct M s hs).val (op U) =
      ∑ i ∈ t, (sectionsMap (Sigma.ι M i) (s i)).val (op U) := by
  classical
  let V : FiniteOpen M s := ⟨U, t.finite_toSet.subset ht⟩
  rw [toCoproduct_eval_finiteOpen M s hs V]
  apply Finset.sum_subset
  · intro i hi
    exact ht i ((FiniteOpen.mem_active_iff M s V i).mp hi)
  · intro i _ hi
    have hz := component_eval_eq_zero M s i U (by
      intro h
      exact hi ((FiniteOpen.mem_active_iff M s V i).mpr h))
    change (Sigma.ι M i).val.app _ ((s i).val _) = 0
    rw [hz]
    exact map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- Projecting a locally finite coproduct section to one summand recovers that component. -/
@[simp]
theorem project_toCoproduct [DecidableEq ι]
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) (i : ι) :
    sectionsMap (Sigma.π M i) (toCoproduct M s hs) = s i := by
  apply (CategoryTheory.Functor.sectionsEquivTerminal
    ((M i).val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) ⊤ isTerminalTop).injective
  change (sectionsMap (Sigma.π M i) (toCoproduct M s hs)).val (op ⊤) =
    (s i).val (op ⊤)
  apply TopCat.Sheaf.eq_of_locally_eq' ((toSheaf 𝒪).obj (M i))
    (fun U : FiniteOpen M s ↦ U.toOpens) ⊤ (fun U ↦ U.toTop)
    (finiteOpen_cover M s hs)
  intro U
  change (M i).val.map U.toTop.op
    ((sectionsMap (Sigma.π M i) (toCoproduct M s hs)).val (op ⊤)) =
      (M i).val.map U.toTop.op ((s i).val (op ⊤))
  rw [PresheafOfModules.sections_property, PresheafOfModules.sections_property]
  change (Sigma.π M i).val.app (op U.toOpens)
    ((toCoproduct M s hs).val (op U.toOpens)) = (s i).val (op U.toOpens)
  rw [toCoproduct_eval_finiteOpen]
  change (Sigma.π M i).val.app (op U.toOpens)
    (∑ j ∈ U.active, (sectionsMap (Sigma.ι M j) (s j)).val (op U.toOpens)) = _
  rw [map_sum]
  have hproj (j : ι) :
      (Sigma.π M i).val.app (op U.toOpens)
          ((sectionsMap (Sigma.ι M j) (s j)).val (op U.toOpens)) =
        if j = i then (s i).val (op U.toOpens) else 0 := by
    by_cases hji : j = i
    · subst j
      rw [if_pos rfl]
      change (sectionsMap (Sigma.π M i) (sectionsMap (Sigma.ι M i) (s i))).val _ = _
      rw [← sectionsMap_comp, Sigma.ι_π_eq_id, sectionsMap_id]
    · rw [if_neg hji]
      change (sectionsMap (Sigma.ι M j ≫ Sigma.π M i) (s j)).val _ = 0
      rw [Sigma.ι_π_of_ne M hji]
      rfl
  simp_rw [hproj]
  by_cases hi : i ∈ U.active
  · simp [hi]
  · have hz := component_eval_eq_zero M s i U.toOpens (by
      intro h
      exact hi ((FiniteOpen.mem_active_iff M s U i).mpr h))
    simpa [hi] using hz.symm

end SectionFamily

namespace Free

-- At these universes, mathlib supplies local bijectivity directly. The scoped attributes below
-- select that proof; proof irrelevance leaves the canonical data definitionally unchanged.

attribute [-instance] TopCat.addCommGrpWEqualsLocallyBijectiveSelf
  TopCat.addCommGrpWEqualsLocallyBijective in
/-- The canonical projection from a free sheaf to one copy of its coefficient sheaf. -/
noncomputable def projection {ι : Type u} [DecidableEq ι] (i : ι) :
    free (R := 𝒪) ι ⟶ unit 𝒪 :=
  Sigma.π (fun _ : ι ↦ unit 𝒪) i

attribute [-instance] TopCat.addCommGrpWEqualsLocallyBijectiveSelf
  TopCat.addCommGrpWEqualsLocallyBijective in
set_option backward.isDefEq.respectTransparency false in
/-- Projecting a section after injectively reindexing its free basis recovers the original
coordinate. -/
@[stacks 01BL "injective free-section reindexing"]
theorem project_freeMap_same {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]
    (e : ι → κ) (he : Function.Injective e)
    (s : (free (R := 𝒪) ι).sections) (i : ι) :
    sectionsMap (projection (e i)) (sectionsMap (freeMap (R := 𝒪) e) s) =
      sectionsMap (projection i) s := by
  have h : freeMap (R := 𝒪) e ≫ projection (e i) = projection i := by
    apply Sigma.hom_ext
    intro j
    change ιFree j ≫ (freeMap e ≫ projection (e i)) =
      ιFree j ≫ projection i
    rw [ιFree_freeMap_assoc]
    by_cases hji : j = i
    · subst j
      simp [projection, ιFree]
    · simp only [projection, ιFree,
        Sigma.ι_π_of_ne _ (fun h ↦ hji (he h)), Sigma.ι_π_of_ne _ hji]
  rw [← sectionsMap_comp, h]

attribute [-instance] TopCat.addCommGrpWEqualsLocallyBijectiveSelf
  TopCat.addCommGrpWEqualsLocallyBijective in
set_option backward.isDefEq.respectTransparency false in
/-- A coordinate outside the range of a free-basis reindexing vanishes on every reindexed
section. -/
@[stacks 01BL "free-section coordinate outside the reindexing range"]
theorem project_freeMap_eq_zero {ι κ : Type u} [DecidableEq κ]
    (e : ι → κ) (s : (free (R := 𝒪) ι).sections) (k : κ)
    (hk : k ∉ Set.range e) :
    sectionsMap (projection k) (sectionsMap (freeMap (R := 𝒪) e) s) = 0 := by
  have h : freeMap (R := 𝒪) e ≫ projection k = 0 := by
    apply Sigma.hom_ext
    intro j
    change ιFree j ≫ (freeMap e ≫ projection k) = ιFree j ≫ 0
    rw [ιFree_freeMap_assoc]
    simpa only [projection, ιFree, comp_zero] using
      Sigma.ι_π_of_ne (fun _ : κ ↦ unit 𝒪) (fun hj ↦ hk ⟨j, hj⟩)
  rw [← sectionsMap_comp, h]
  apply PresheafOfModules.sections_ext
  intro U
  change (0 : (free (R := 𝒪) ι) ⟶ unit 𝒪).val.app U (s.val U) = 0
  rfl

attribute [-instance] TopCat.addCommGrpWEqualsLocallyBijectiveSelf
  TopCat.addCommGrpWEqualsLocallyBijective in
/-- A locally finite family of scalar sections determines a section of a free sheaf. -/
@[stacks 01BL "locally finite free section"]
noncomputable def sectionOfLocallyFinite {ι : Type u}
    (s : ι → (unit 𝒪).sections)
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) :
    (free (R := 𝒪) ι).sections :=
  SectionFamily.toCoproduct (fun _ ↦ unit 𝒪) s hs

attribute [-instance] TopCat.addCommGrpWEqualsLocallyBijectiveSelf
  TopCat.addCommGrpWEqualsLocallyBijective in
/-- Projecting a locally finite section of a free sheaf recovers its chosen coefficient. -/
@[simp]
theorem project_sectionOfLocallyFinite {ι : Type u} [DecidableEq ι]
    (s : ι → (unit 𝒪).sections)
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) (i : ι) :
    sectionsMap (projection i) (sectionOfLocallyFinite s hs) = s i := by
  exact SectionFamily.project_toCoproduct (fun _ ↦ unit 𝒪) s hs i

attribute [-instance] TopCat.addCommGrpWEqualsLocallyBijectiveSelf
  TopCat.addCommGrpWEqualsLocallyBijective in
/-- A componentwise locally finite coefficient family determines a morphism between free sheaves. -/
@[stacks 01BL "locally finite free sheaf morphism"]
noncomputable def homOfLocallyFinite {ι κ : Type u}
    (a : ι → κ → (unit 𝒪).sections)
    (ha : ∀ i, LocallyFinite fun k ↦ sectionSupport (a i k)) :
    free (R := 𝒪) ι ⟶ free (R := 𝒪) κ :=
  (freeHomEquiv (free (R := 𝒪) κ)).symm
    (fun i ↦ sectionOfLocallyFinite (a i) (ha i))

attribute [-instance] TopCat.addCommGrpWEqualsLocallyBijectiveSelf
  TopCat.addCommGrpWEqualsLocallyBijective in
/-- Evaluating `homOfLocallyFinite` on a basis vector gives its locally finite coefficient
family. -/
theorem freeHomEquiv_homOfLocallyFinite {ι κ : Type u}
    (a : ι → κ → (unit 𝒪).sections)
    (ha : ∀ i, LocallyFinite fun k ↦ sectionSupport (a i k)) (i : ι) :
    freeHomEquiv (free (R := 𝒪) κ) (homOfLocallyFinite a ha) i =
      sectionOfLocallyFinite (a i) (ha i) := by
  exact congrFun ((freeHomEquiv (free (R := 𝒪) κ)).apply_symm_apply _) i

end Free

end SheafOfModules
