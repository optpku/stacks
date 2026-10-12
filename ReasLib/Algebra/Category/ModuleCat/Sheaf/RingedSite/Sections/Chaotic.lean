/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sections.BaseChange
public import ReasLib.Algebra.Category.Ring.Presheaf.Flat
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre.NaturalTransformation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change on a chaotic ringed site

Evaluation is exact on a chaotic site.  Consequently the presheaf-owned base-change source is
exact along flat restriction maps, and the isomorphism locus of all base-change comparisons is a
weak Serre class.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Presheaf

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.Chaotic.BaseChange

variable {C : Type u} [Category.{v} C]
variable (O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Lemma 18.24.3 (0GZN): evaluation at an object is exact for module sheaves on the chaotic
topology. -/
@[stacks 0GZN "exactness of evaluation on a chaotic site"]
theorem evaluation_exact (U : C) :
    exactFunctor
      (ringedSiteModuleCategory.{u, v, max w z, w}
        (⊥ : GrothendieckTopology C) O)
      (ModuleCat.{max w z} (O.obj.obj (Opposite.op U)))
      (SheafOfModules.RingedSite.BaseChange.evaluation O U) := sorry

/-- Lemma 18.24.4 (0GZP): base change along a flat restriction map is exact on a chaotic
site. -/
@[stacks 0GZP "exact base change on sections"]
theorem functor_exact_of_flat {U V : C} (f : U ⟶ V)
    (hf : CommRingCat.flat (O.obj.map f.op)) :
    exactFunctor
      (ringedSiteModuleCategory.{u, v, max w z, w}
        (⊥ : GrothendieckTopology C) O)
      (ModuleCat.{max w z} (O.obj.obj (Opposite.op U)))
      (SheafOfModules.RingedSite.BaseChange.functor O f) := sorry

section WeakSerre

variable [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{max w z}]
variable [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective
  AddCommGrpCat.{max w z}]

/-- Lemma 18.24.4 (0GZP): if the coefficient presheaf has flat restriction maps, its
base-change-compatible module sheaves form a weak Serre class on the chaotic topology. -/
@[stacks 0GZP "base-change-compatible weak Serre class"]
theorem compatible_isWeakSerreClass [Restriction.Flat O.obj] :
    ObjectProperty.IsWeakSerreClass
      (SheafOfModules.RingedSite.BaseChange.compatible O) := sorry

attribute [instance] compatible_isWeakSerreClass

end WeakSerre

end SheafOfModules.RingedSite.Chaotic.BaseChange
