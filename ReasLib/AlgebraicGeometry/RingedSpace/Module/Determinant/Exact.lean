/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant.Exact.Descent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Determinant
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants of exact sequences on ringed spaces

This file specializes the choice-free determinant descent API to the opens site of a ringed
space.  A comparison morphism is characterized by the split determinant formula on some cover;
the cover and splittings occur only in this local Prop-valued characterization, while the
candidate global morphism remains explicit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Determinant.Exact

variable {X : RingedSpace.{u}} {S : ShortComplex X.Modules}

/-- The local exact-sequence determinant formula on an explicitly supplied cover with explicitly
supplied splittings. -/
@[stacks 0B38 "local determinant formula on a ringed space"]
abbrev IsFormula
    {I : Type u} (U : I → Opens X)
    (s : ∀ i,
      (S.map (SheafOfModules.Localization.restriction X.ringCatSheaf (U i))).Splitting)
    (g : det(S.X₁) ⊗ det(S.X₃) ⟶ det(S.X₂)) : Prop :=
  SheafOfModules.RingedSite.Determinant.Exact.IsFormula
    (J := Opens.grothendieckTopology X) (S := S) X.sheaf U s g

/-- A morphism is the determinant comparison for a short complex when it satisfies the split
determinant formula locally on some cover.  The existential witnesses express a local property
of the displayed morphism; they are not used to choose the morphism. -/
@[stacks 0B38 "determinant comparison on a ringed space"]
def IsComparison (g : det(S.X₁) ⊗ det(S.X₃) ⟶ det(S.X₂)) : Prop :=
  ∃ (I : Type u) (U : I → Opens X),
    (Opens.grothendieckTopology X).CoversTop U ∧
      ∃ s : ∀ i,
        (S.map (SheafOfModules.Localization.restriction X.ringCatSheaf (U i))).Splitting,
        IsFormula U s g

/-- A morphism satisfying the local split formula on a covering family is a determinant
comparison. -/
@[stacks 0B38 "constructing the local determinant comparison property"]
theorem isComparison_of_formula
    {I : Type u} {U : I → Opens X}
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (s : ∀ i,
      (S.map (SheafOfModules.Localization.restriction X.ringCatSheaf (U i))).Splitting)
    {g : det(S.X₁) ⊗ det(S.X₃) ⟶ det(S.X₂)} (hg : IsFormula U s g) :
    IsComparison g := sorry

namespace IsFormula

/-- A morphism satisfying the split determinant formula restricts to an isomorphism on each
member of the splitting family when both endpoint module sheaves are finite locally free. -/
@[stacks 0B38 "local invertibility of the ringed-space determinant comparison"]
theorem isIso_restriction
    {I : Type u} {U : I → Opens X}
    (s : ∀ i,
      (S.map (SheafOfModules.Localization.restriction X.ringCatSheaf (U i))).Splitting)
    (g : det(S.X₁) ⊗ det(S.X₃) ⟶ det(S.X₂))
    (hg : IsFormula U s g) (i : I)
    [SheafOfModules.IsFiniteLocallyFree S.X₁]
    [SheafOfModules.IsFiniteLocallyFree S.X₃] :
    IsIso ((SheafOfModules.Localization.restriction X.ringCatSheaf (U i)).map g) := sorry

end IsFormula

/-- Two determinant comparison morphisms for the same short complex are equal. -/
@[stacks 0B38 "uniqueness of the ringed-space determinant comparison"]
theorem comparison_unique
    {g h : det(S.X₁) ⊗ det(S.X₃) ⟶ det(S.X₂)}
    (hg : IsComparison g) (hh : IsComparison h) : g = h := sorry

/-- A short exact complex ending in a finite locally free module sheaf has a unique determinant
comparison morphism.  This statement records existence and canonicality without choosing
non-Prop data from provisional gluing proofs. -/
@[stacks 0B38 "existence and uniqueness of the ringed-space determinant comparison"]
theorem existsUnique_comparison
    (hS : S.ShortExact) [SheafOfModules.IsFiniteLocallyFree S.X₃] :
    ∃! g : det(S.X₁) ⊗ det(S.X₃) ⟶ det(S.X₂), IsComparison g := sorry

/-- A determinant comparison is invertible when the two endpoint module sheaves are finite
locally free. -/
@[stacks 0B38 "invertibility of the ringed-space determinant comparison"]
theorem comparison_isIso
    (g : det(S.X₁) ⊗ det(S.X₃) ⟶ det(S.X₂)) (hg : IsComparison g)
    [SheafOfModules.IsFiniteLocallyFree S.X₁]
    [SheafOfModules.IsFiniteLocallyFree S.X₃] : IsIso g := sorry

/-- For a short exact complex with finite locally free endpoints, the local formula uniquely
characterizes an invertible determinant comparison morphism. -/
@[stacks 0B38 "canonical invertible determinant comparison on a ringed space"]
theorem existsUnique_comparison_isIso
    (hS : S.ShortExact)
    [SheafOfModules.IsFiniteLocallyFree S.X₁]
    [SheafOfModules.IsFiniteLocallyFree S.X₃] :
    ∃! g : det(S.X₁) ⊗ det(S.X₃) ⟶ det(S.X₂), IsComparison g ∧ IsIso g := sorry

/-- A short exact complex with finite locally free endpoints has a unique determinant
comparison isomorphism. -/
@[stacks 0B38 "canonical determinant isomorphism of a short exact sequence"]
theorem existsUnique_comparisonIso
    (hS : S.ShortExact)
    [SheafOfModules.IsFiniteLocallyFree S.X₁]
    [SheafOfModules.IsFiniteLocallyFree S.X₃] :
    ∃! e : det(S.X₁) ⊗ det(S.X₃) ≅ det(S.X₂), IsComparison e.hom := sorry

end AlgebraicGeometry.RingedSpace.Determinant.Exact
