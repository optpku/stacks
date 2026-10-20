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
    differential R Uᵢ π ≫ augmentation R Uᵢ π = 0 := sorry

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
    Epi (augmentation R Uᵢ π) := sorry

/-- Lemma 18.30.2: a covering family of a quasi-compact object contains a finite subfamily whose
augmented Čech complex is exact and whose augmentation is an epimorphism. -/
@[stacks 0G1W "sieve-saturated specialization"]
theorem exists_finset_exact_and_epi {I : Type z} {U : C}
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasFiniteCoproducts (SheafOfModules.{w} R)]
    (hU : J.QuasiCompactObject U) (hcover : Sieve.ofArrows Uᵢ π ∈ J U) :
    ∃ K : Finset I,
      (shortComplex R (fun i : K ↦ Uᵢ i) (fun i ↦ π i)).Exact ∧
        Epi (augmentation R (fun i : K ↦ Uᵢ i) (fun i ↦ π i)) := sorry

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
    (shortComplex R Uᵢ π).Exact := sorry

/-- Lemma 18.30.1 (0934) (2): the Čech augmentation of a chosen covering family is an
epimorphism. -/
@[stacks 0934 "(2)"]
theorem augmentationEpiOfCoverage {I : Type z} {U : C}
    (Uᵢ : I → C) (π : ∀ i, Uᵢ i ⟶ U)
    [HasCoproductsOfShape I (SheafOfModules.{w} R)]
    (hcover : Presieve.ofArrows Uᵢ π ∈ K U) :
    Epi (augmentation R Uᵢ π) := sorry

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
        (fun i : T ↦ Uᵢ i) (fun i ↦ π i)) := sorry

end CategoryTheory.Coverage.QuasiCompactObject
