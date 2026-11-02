/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
public import ReasLib.CategoryTheory.Sites.QuasiCompact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Čech presentations by localized structure modules

A covering family `Uᵢ ⟶ U` determines an augmented Čech short complex of localized
structure modules.  The maps are explicit coproduct maps built from
`Localization.structureModuleMap`; exactness is stated separately from the construction so that
the same data can be reused independently of the covering hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe z w v u

namespace SheafOfModules.Localization.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]
variable (R : Sheaf J RingCat.{w})
variable [∀ U : C, (restriction R U : SheafOfModules.{w} R ⥤
  SheafOfModules.{w} (R.over U)).IsRightAdjoint]

omit [HasPullbacks C] in
private theorem homEquiv_comp (U : C) {M N : SheafOfModules.{w} R}
    (f : structureModule R U ⟶ M) (g : M ⟶ N) :
    structureModuleHomEquiv R U N (f ≫ g) =
      g.val.app (Opposite.op U) (structureModuleHomEquiv R U M f) := by
  unfold structureModuleHomEquiv
  simp only [Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

omit [HasPullbacks C] in
private theorem map_homEquiv {U V : C} (f : U ⟶ V)
    (M : SheafOfModules.{w} R) (α : structureModule R V ⟶ M) :
    structureModuleHomEquiv R U M (structureModuleMap R f ≫ α) =
      M.val.map f.op (structureModuleHomEquiv R V M α) := by
  rw [homEquiv_comp]
  unfold structureModuleMap
  rw [Equiv.apply_symm_apply, PresheafOfModules.naturality_apply]
  congr 1

omit [HasPullbacks C] in
private theorem map_comp {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    structureModuleMap R (f ≫ g) = structureModuleMap R f ≫ structureModuleMap R g := by
  apply (structureModuleHomEquiv R U (structureModule R W)).injective
  rw [map_homEquiv]
  simp only [structureModuleMap, Equiv.apply_symm_apply, op_comp]
  exact (structureModule R W).val.map_comp_apply g.op f.op _

/-- The component of the Čech differential associated to a pair of covering arrows. -/
noncomputable def differentialComponent {I : Type z} {U : C}
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U) [HasCoproductsOfShape I (SheafOfModules.{w} R)]
    (p : I × I) :
    structureModule R (Limits.pullback (π p.1) (π p.2)) ⟶
      (∐ fun i ↦ structureModule R (Uᵢ i)) :=
  structureModuleMap R (Limits.pullback.fst (π p.1) (π p.2)) ≫
      Sigma.ι (fun i ↦ structureModule R (Uᵢ i)) p.1 -
    structureModuleMap R (Limits.pullback.snd (π p.1) (π p.2)) ≫
      Sigma.ι (fun i ↦ structureModule R (Uᵢ i)) p.2

/-- The first differential in the augmented Čech complex of a family `Uᵢ ⟶ U`. -/
@[stacks 0934 "Čech differential"]
noncomputable def differential {I : Type z} {U : C}
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasCoproductsOfShape I (SheafOfModules.{w} R)]
    [HasCoproductsOfShape (I × I) (SheafOfModules.{w} R)] :
    (∐ fun p : I × I ↦ structureModule R (Limits.pullback (π p.1) (π p.2))) ⟶
      (∐ fun i ↦ structureModule R (Uᵢ i)) :=
  Sigma.desc (differentialComponent R Uᵢ π)

/-- The augmentation in the Čech complex of a family `Uᵢ ⟶ U`. -/
@[stacks 0934 "Čech augmentation"]
noncomputable def augmentation {I : Type z} {U : C}
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasCoproductsOfShape I (SheafOfModules.{w} R)] :
    (∐ fun i ↦ structureModule R (Uᵢ i)) ⟶ structureModule R U :=
  Sigma.desc fun i ↦ structureModuleMap R (π i)

/-- The Čech differential followed by the augmentation is zero. -/
theorem differential_comp_augmentation {I : Type z} {U : C}
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasCoproductsOfShape I (SheafOfModules.{w} R)]
    [HasCoproductsOfShape (I × I) (SheafOfModules.{w} R)] :
    differential R Uᵢ π ≫ augmentation R Uᵢ π = 0 := by
  apply Sigma.hom_ext
  intro p
  simp only [differential, Sigma.ι_desc_assoc, differentialComponent,
    Preadditive.sub_comp, Category.assoc, augmentation, Sigma.ι_desc,
    ← map_comp, Limits.pullback.condition, sub_self, comp_zero]

/-- The augmented Čech short complex associated to a family of arrows `Uᵢ ⟶ U`. -/
@[stacks 0934 "Čech short complex"]
noncomputable def shortComplex {I : Type z} {U : C}
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasCoproductsOfShape I (SheafOfModules.{w} R)]
    [HasCoproductsOfShape (I × I) (SheafOfModules.{w} R)] :
    ShortComplex (SheafOfModules.{w} R) :=
  ShortComplex.mk (differential R Uᵢ π) (augmentation R Uᵢ π)
    (differential_comp_augmentation R Uᵢ π)

/-- Lemma 18.30.1 (1): the augmented Čech complex of a covering family is exact at its middle
term. -/
@[stacks 0934 "(1), sieve-saturated specialization"]
theorem exact {I : Type z} {U : C} (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasCoproductsOfShape I (SheafOfModules.{w} R)]
    [HasCoproductsOfShape (I × I) (SheafOfModules.{w} R)]
    (hcover : Sieve.ofArrows Uᵢ π ∈ J U) :
    (shortComplex R Uᵢ π).Exact := sorry

/-- Lemma 18.30.1 (2): the Čech augmentation of a covering family is an epimorphism. -/
@[stacks 0934 "(2), sieve-saturated specialization"]
theorem augmentation_epi {I : Type z} {U : C} (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasCoproductsOfShape I (SheafOfModules.{w} R)]
    (hcover : Sieve.ofArrows Uᵢ π ∈ J U) :
    Epi (augmentation R Uᵢ π) := by
  constructor
  intro M a b hab
  apply (structureModuleHomEquiv R U M).injective
  let P := M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat
  have hM : Presieve.IsSheaf J P :=
    (isSheaf_iff_isSheaf_of_type J P).mp
      (Presheaf.isSheaf_comp_of_isSheaf J _ _ M.isSheaf)
  apply (hM.isSheafFor (Presieve.ofArrows Uᵢ π) hcover).isSeparatedFor.ext
  rintro V f ⟨i⟩
  change M.val.map (π i).op _ = M.val.map (π i).op _
  rw [← map_homEquiv, ← map_homEquiv]
  apply congrArg (structureModuleHomEquiv R (Uᵢ i) M)
  simpa only [Category.assoc, augmentation, Sigma.ι_desc_assoc] using
    congrArg (fun k ↦ Sigma.ι (fun i ↦ structureModule R (Uᵢ i)) i ≫ k) hab

/-- Lemma 18.30.2: a covering family of a quasi-compact object contains a finite subfamily whose
augmented Čech complex is exact and whose augmentation is an epimorphism. -/
@[stacks 0G1W "sieve-saturated specialization"]
theorem exists_finset_exact_and_epi {I : Type z} {U : C}
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasFiniteCoproducts (SheafOfModules.{w} R)]
    (hU : J.QuasiCompactObject U) (hcover : Sieve.ofArrows Uᵢ π ∈ J U) :
    ∃ K : Finset I,
      (shortComplex R (fun i : K ↦ Uᵢ i) (fun i ↦ π i)).Exact ∧
        Epi (augmentation R (fun i : K ↦ Uᵢ i) (fun i ↦ π i)) := by
  classical
  let S : J.Cover U := ⟨Sieve.ofArrows Uᵢ π, hcover⟩
  obtain ⟨T, hT, hTcover⟩ := hU S
  let α : T → I := fun t ↦ Sieve.ofArrows.i t.1.hf
  letI : Finite T := hT.to_subtype
  have hα := Set.finite_range α
  let F : Finset I := hα.toFinset
  have hF : Sieve.ofArrows (fun i : F ↦ Uᵢ i) (fun i ↦ π i) ∈ J U := by
    apply J.superset_covering ?_ hTcover
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro t
    let j : F := ⟨α t, hα.mem_toFinset.mpr ⟨t, rfl⟩⟩
    rw [← Sieve.ofArrows.fac t.1.hf]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ j) _
  exact ⟨F, exact R _ _ hF, augmentation_epi R _ _ hF⟩

end SheafOfModules.Localization.Cech

namespace SheafOfModules.Localization.Cech

variable {C : Type u} [Category.{v} C] {K : Coverage C} [HasPullbacks C]
variable (R : Sheaf K.toGrothendieck RingCat.{w})
variable [∀ U : C, (restriction R U : SheafOfModules.{w} R ⥤
  SheafOfModules.{w} (R.over U)).IsRightAdjoint]

/-- Lemma 18.30.1 (0934) (1): the augmented Čech complex of a chosen covering family is exact
at its middle term. -/
@[stacks 0934 "(1)"]
theorem exactOfCoverage {I : Type z} {U : C}
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasCoproductsOfShape I (SheafOfModules.{w} R)]
    [HasCoproductsOfShape (I × I) (SheafOfModules.{w} R)]
    (hcover : Presieve.ofArrows Uᵢ π ∈ K U) :
    (shortComplex R Uᵢ π).Exact := by
  exact exact R Uᵢ π (K.mem_toGrothendieck_sieves_of_superset (Sieve.le_generate _) hcover)

/-- Lemma 18.30.1 (0934) (2): the Čech augmentation of a chosen covering family is an
epimorphism. -/
@[stacks 0934 "(2)"]
theorem augmentationEpiOfCoverage {I : Type z} {U : C}
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasCoproductsOfShape I (SheafOfModules.{w} R)]
    (hcover : Presieve.ofArrows Uᵢ π ∈ K U) :
    Epi (augmentation R Uᵢ π) := by
  exact augmentation_epi R Uᵢ π
    (K.mem_toGrothendieck_sieves_of_superset (Sieve.le_generate _) hcover)

end SheafOfModules.Localization.Cech

namespace CategoryTheory.Coverage.QuasiCompactObject

variable {C : Type u} [Category.{v} C] {K : Coverage C} [HasPullbacks C]

/-- Lemma 18.30.2 (0G1W): a chosen covering family of a quasi-compact site object contains a
finite subfamily whose augmented Čech sequence is exact. -/
@[stacks 0G1W]
theorem existsFiniteCechExact {I : Type z} {U : C}
    (hU : K.QuasiCompactObject U) (R : Sheaf K.toGrothendieck RingCat.{w})
    [∀ V : C, (SheafOfModules.Localization.restriction R V :
      SheafOfModules.{w} R ⥤ SheafOfModules.{w} (R.over V)).IsRightAdjoint]
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasFiniteCoproducts (SheafOfModules.{w} R)]
    (hcover : Presieve.ofArrows Uᵢ π ∈ K U) :
    ∃ T : Finset I,
      (SheafOfModules.Localization.Cech.shortComplex R
        (fun i : T ↦ Uᵢ i) (fun i ↦ π i)).Exact ∧
      Epi (SheafOfModules.Localization.Cech.augmentation R
        (fun i : T ↦ Uᵢ i) (fun i ↦ π i)) := by
  classical
  obtain ⟨S, hS, T, hT, hST⟩ := hU (Presieve.ofArrows Uᵢ π) hcover
  let α : T → I := fun t ↦ Presieve.ofArrows.idx t.1.2
  letI : Finite T := hT.to_subtype
  have hα := Set.finite_range α
  let F : Finset I := hα.toFinset
  have hF : Sieve.ofArrows (fun i : F ↦ Uᵢ i) (fun i ↦ π i) ∈ K.toGrothendieck U := by
    apply K.mem_toGrothendieck_sieves_of_superset ?_ hS
    intro V f hf
    obtain ⟨W, g, e, he, hge⟩ := hST hf
    rcases he with ⟨t⟩
    let j : F := ⟨α t, hα.mem_toFinset.mpr ⟨t, rfl⟩⟩
    have ht : Sieve.ofArrows (fun i : F ↦ Uᵢ i) (fun i ↦ π i) t.1.1.2 := by
      rw [Presieve.ofArrows.eq_eqToHom_comp_hom_idx t.1.2]
      exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ j) _
    rw [← hge]
    exact Sieve.downward_closed _ ht _
  exact ⟨F, SheafOfModules.Localization.Cech.exact R _ _ hF,
    SheafOfModules.Localization.Cech.augmentation_epi R _ _ hF⟩

end CategoryTheory.Coverage.QuasiCompactObject
