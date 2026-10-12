/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sequential.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sequential.HomologicalComplex
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Realizing derived module towers

This file relates a compatible tower of derived modules over a sequential inverse system of rings
to a single object in the derived category of the varying-ring module category.

@stack 091I
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedTower

-- Local instance justification (defeq pin): realization uses the standard derived categories of
-- the Grothendieck varying-ring module category and of the stagewise module categories.
attribute [local instance] HasDerivedCategory.standard

variable {F : SequentialInverseSystem CommRingCat.{u}}

/-- The derived module tower obtained by evaluating a cochain complex of varying-ring modules at
each stage.  Its successor morphisms are induced by the actual cochain-level transition maps. -/
@[stacks 091I "tower obtained from a cochain realization"]
noncomputable def ofCochainComplex
    (M : CochainComplex (SequentialInverseSystem.ModuleSystem.{u, u} F) ℤ) :
    DerivedTower F where
  obj n := DerivedCategory.Q.obj (SequentialInverseSystem.cochainEval F n M)
  step n :=
    DerivedCategory.Q.map ((SequentialInverseSystem.cochainEvaluationStep F n).app M) ≫
      ((ModuleCat.restrictScalars (F.stepMap n).hom).mapDerivedCategoryFactors.inv.app
        (SequentialInverseSystem.cochainEval F n M))

/-- A realization of `T` by `K` consists of a cochain representative of `K` and compatible
stagewise identifications of its evaluations with the stages of `T`. -/
@[stacks 091I "realization of a compatible derived module tower"]
structure Realization (T : DerivedTower F)
    (K : DerivedCategory (SequentialInverseSystem.ModuleSystem.{u, u} F)) where
  /-- A cochain representative of the realizing derived object. -/
  representative : CochainComplex (SequentialInverseSystem.ModuleSystem.{u, u} F) ℤ
  /-- Identification of the chosen representative with the realizing derived object. -/
  objectIso : DerivedCategory.Q.obj representative ≅ K
  /-- The stagewise identification with the prescribed derived module tower. -/
  stageIso (n : ℕ) : (ofCochainComplex representative).obj n ≅ T.obj n
  /-- The stagewise identifications intertwine the cochain transition maps with the prescribed
  tower transitions. -/
  naturality (n : ℕ) :
    CommSq
      ((ofCochainComplex representative).step n)
      (stageIso (n + 1)).hom
      ((derivedRestrictionOfScalars (F.stepMap n).hom).map (stageIso n).hom)
      (T.step n)

/-- Lemma 15.88.5 (091I): every compatible tower of derived modules over a sequential inverse
system of rings is realized by an object in the derived category of varying-ring modules, with
compatible stagewise isomorphisms. -/
@[stacks 091I]
theorem existsRealization (T : DerivedTower F) :
    ∃ K : DerivedCategory (SequentialInverseSystem.ModuleSystem.{u, u} F),
      Nonempty (T.Realization K) := sorry

end CategoryTheory.ModuleCat.DerivedTower
