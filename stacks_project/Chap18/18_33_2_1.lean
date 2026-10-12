/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Differentials.Relations
import StacksCheckRecall

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open SheafOfModules.DifferentialRelations

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O₁ O₂ : Sheaf J RingCat.{w}} (φ : O₁ ⟶ O₂)

/- Equation 18.33.2.1 (04BM): the three free module sheaves are sheafifications
of the pointwise free modules on local pairs, local pairs, and local O₁ sections.
Their relation map sends the three generator families to the displayed additive,
Leibniz, and base-ring relations in the free O₂-module sheaf on O₂. -/
@[stacks 04BM "generator-relations map for relative differentials"] #check
  (relationMap φ :
    ((pairGenerators O₂ ⨿ pairGenerators O₂) ⨿
      freeSheaf O₂ (O₁.obj ⋙ forget RingCat)) ⟶ generators O₂)

#check @SheafOfModules.DifferentialRelations.addMap_generator
#check @SheafOfModules.DifferentialRelations.mulMap_generator
#check @SheafOfModules.DifferentialRelations.baseMap_generator
#check @SheafOfModules.DifferentialRelations.relationMap_generators
