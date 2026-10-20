/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.Sequential
public import ReasLib.CategoryTheory.DerivedCategory.Colimit.Sequential
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Homological.SelectedCoproduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Represented Hom and sequential colimits

@stack 07LR

This leaf owns the concrete represented-Hom comparison attached to the canonical homotopy-colimit
presentation of a termwise sequential colimit in a derived category.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open DerivedCategory

universe u

-- Local instance justification (search instability): the comparison is formed in the standard
-- t-structure on the derived category of modules.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [Ring R]

/-- The represented-Hom comparison attached to a termwise sequential colimit. -/
@[stacks 07LR "source comparison morphism"]
noncomputable def compactSequentialHomComparison
    (K : DerivedCategory (ModuleCat.{u} R))
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) :
    colimit ((S ⋙ Q) ⋙ preadditiveCoyoneda.obj (op K)) ⟶
      (preadditiveCoyoneda.obj (op K)).obj (Q.obj (colimit S)) :=
  HomotopyColimit.Presentation.imageComparison
    (SequentialColimit.presentation S)
    (preadditiveCoyoneda.obj (op K))

/-- Lemma 15.79.2 (07LR): preserving countable coproducts makes the represented-Hom comparison
for a termwise sequential colimit an isomorphism. -/
@[stacks 07LR "sequential represented-Hom comparison"]
theorem compactSequentialHomComparison_isIso
    (K : DerivedCategory (ModuleCat.{u} R))
    [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (compactSequentialHomComparison K S) := sorry

end CategoryTheory.DerivedCategory
