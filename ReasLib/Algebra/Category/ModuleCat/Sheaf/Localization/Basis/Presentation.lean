/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Compact
public import ReasLib.CategoryTheory.Presentation.Finite.WeakSerre
public import ReasLib.CategoryTheory.Sites.QuasiCompact.Basis.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module presentations from a quasi-compact basis

Localized structure modules attached to basis objects are treated as the values of the functor
`Localization.structureModuleFunctor`.  Finite presentations, filtered generation, and closure
properties are then expressed through reusable `ObjectProperty` APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace SheafOfModules.Localization.Basis

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (R : Sheaf J RingCat.{w}) (B : Set C)
variable [∀ U : C, (restriction R U : SheafOfModules.{w} R ⥤
  SheafOfModules.{w} (R.over U)).IsRightAdjoint]

/-- Equation 18.30.7.2: the property of admitting a cokernel presentation by a map between
finite coproducts of localized structure modules associated to objects of `B`. -/
@[stacks 093D]
abbrev finitePresentation : ObjectProperty (SheafOfModules.{w} R) :=
  (structureModuleFunctor R).finiteCokernelPresentation B

/-- Lemma 18.30.6 (093B) (2), sieve-saturated specialization: enough objects in `B` give an
epimorphism from a coproduct of localized structure modules to every module sheaf. -/
@[stacks 093B "(2), sieve-saturated specialization"]
theorem exists_epi_from_coproduct
    [HasCoproducts.{max u v w} (SheafOfModules.{w} R)]
    (h_enough : J.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (M : SheafOfModules.{w} R) :
    ∃ (I : Type (max u v w)) (U : I → C),
      (∀ i, U i ∈ B) ∧
        ∃ f : (∐ fun i ↦ structureModule R (U i)) ⟶ M, Epi f := sorry

/-- Lemma 18.30.7 (093C) (2), sieve-saturated specialization: enough basis objects and
Grothendieck-topology quasi-compactness generate every module sheaf by finite presentations. -/
@[stacks 093C "(2), sieve-saturated specialization"]
theorem finitePresentation_ind
    (h_enough : J.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (h_compact : GrothendieckTopology.Basis.IsQuasiCompact J B)
    (M : SheafOfModules.{w} R) :
    (finitePresentation R B).ind M := sorry

/-- Lemma 18.30.8 (093E), sieve-saturated specialization: finite basis presentations are closed
under cokernels. -/
@[stacks 093E "sieve-saturated specialization"]
theorem finitePresentation_isClosedUnderCokernels
    (h_enough : J.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (h_compact : GrothendieckTopology.Basis.IsQuasiCompact J B) :
    (finitePresentation R B).IsClosedUnderCokernels := sorry

/-- Lemma 18.30.10 (093G), sieve-saturated specialization: quasi-compact pairwise overlaps make
finite basis presentations closed under extensions. -/
@[stacks 093G "sieve-saturated specialization"]
theorem finitePresentation_isClosedUnderExtensions
    (h_enough : J.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (h_compact : GrothendieckTopology.Basis.IsQuasiCompact J B)
    (h_overlaps : GrothendieckTopology.Basis.HasQuasiCompactOverlaps J B) :
    (finitePresentation R B).IsClosedUnderExtensions := sorry

/-- Lemma 18.30.11 (093H), sieve-saturated specialization: the generator-kernel condition makes
finite basis presentations a weak Serre class. -/
@[stacks 093H "sieve-saturated specialization"]
theorem finitePresentation_isWeakSerreClass
    [Abelian (SheafOfModules.{w} R)]
    (h_enough : J.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (h_compact : GrothendieckTopology.Basis.IsQuasiCompact J B)
    (h_overlaps : GrothendieckTopology.Basis.HasQuasiCompactOverlaps J B)
    (h_kernels : CategoryTheory.Functor.FiniteCokernelPresentation.HasKernels
      (structureModuleFunctor R) B) :
    ObjectProperty.IsWeakSerreClass (finitePresentation R B) := sorry

end SheafOfModules.Localization.Basis

namespace SheafOfModules.Localization.Basis

variable {C : Type u} [Category.{v} C] {K : Coverage C}
variable [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (R : Sheaf K.toGrothendieck RingCat.{w}) (B : Set C)
variable [∀ U : C, (restriction R U : SheafOfModules.{w} R ⥤
  SheafOfModules.{w} (R.over U)).IsRightAdjoint]

/-- Lemma 18.30.6 (093B) (2): enough objects for a chosen coverage give an epimorphism from a
coproduct of localized structure modules to every module sheaf. -/
@[stacks 093B "(2)"]
theorem existsEpiFromCoproduct
    [HasCoproducts.{max u v w} (SheafOfModules.{w} R)]
    (hEnough : K.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (M : SheafOfModules.{w} R) :
    ∃ (I : Type (max u v w)) (U : I → C),
      (∀ i, U i ∈ B) ∧
        ∃ f : (∐ fun i ↦ structureModule R (U i)) ⟶ M, Epi f := sorry

/-- Lemma 18.30.7 (093C) (2): enough basis objects that are quasi-compact for a chosen coverage
generate every module sheaf under filtered colimits of finite basis presentations. -/
@[stacks 093C "(2)"]
theorem finitePresentationInd
    (hEnough : K.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (hCompact : CategoryTheory.Coverage.Basis.IsQuasiCompact K B)
    (M : SheafOfModules.{w} R) :
    (finitePresentation R B).ind M := sorry

/-- Lemma 18.30.8 (093E): under chosen-cover basis covering and quasi-compactness, finite basis
presentations are closed under cokernels. -/
@[stacks 093E]
theorem finitePresentationClosedUnderCokernels
    (hEnough : K.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (hCompact : CategoryTheory.Coverage.Basis.IsQuasiCompact K B) :
    (finitePresentation R B).IsClosedUnderCokernels := sorry

/-- Lemma 18.30.10 (093G): quasi-compact pairwise overlaps for chosen basis covers make finite
basis presentations closed under extensions. -/
@[stacks 093G]
theorem finitePresentationClosedUnderExtensions
    (hEnough : K.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (hCompact : CategoryTheory.Coverage.Basis.IsQuasiCompact K B)
    (hOverlaps : CategoryTheory.Coverage.Basis.HasQuasiCompactOverlaps K B) :
    (finitePresentation R B).IsClosedUnderExtensions := sorry

/-- Lemma 18.30.11 (093H): under the chosen-cover basis hypotheses, the generator-kernel
condition makes finite basis presentations a weak Serre class. -/
@[stacks 093H]
theorem finitePresentationIsWeakSerreClass
    [Abelian (SheafOfModules.{w} R)]
    (hEnough : K.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (hCompact : CategoryTheory.Coverage.Basis.IsQuasiCompact K B)
    (hOverlaps : CategoryTheory.Coverage.Basis.HasQuasiCompactOverlaps K B)
    (hKernels : CategoryTheory.Functor.FiniteCokernelPresentation.HasKernels
      (structureModuleFunctor R) B) :
    ObjectProperty.IsWeakSerreClass (finitePresentation R B) := sorry

end SheafOfModules.Localization.Basis
