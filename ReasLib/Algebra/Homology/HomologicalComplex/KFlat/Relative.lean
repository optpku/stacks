/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative K-flat homological complexes

This file owns K-flatness relative to an arbitrary bifunctor and a chosen totalization shape.
The source complex, the K-flat complex, and their total complex may have different shapes.
Monoidal K-flatness and category-specific specializations live in downstream leaves.
@stack 06XZ
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w

namespace HomologicalComplex

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
variable {I₁ : Type w₁} {I₂ : Type w₂} {J : Type w}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape J}

/-- Relative K-flatness for a bifunctor and chosen shapes: totalized application in the first
variable sends acyclic `c₁`-complexes to acyclic `c`-complexes. -/
@[stacks 06XZ "bifunctor-relative homological-complex form"]
def IsKFlatFor (K : HomologicalComplex C₂ c₂) (F : C₁ ⥤ C₂ ⥤ D)
    (c₁ : ComplexShape I₁) (c : ComplexShape J)
    [TotalComplexShape c₁ c₂ c] [DecidableEq J]
    [F.PreservesZeroMorphisms] [∀ X : C₁, (F.obj X).PreservesZeroMorphisms] : Prop :=
  ∀ ⦃M : HomologicalComplex C₁ c₁⦄ [HasMapBifunctor M K F c],
    M.Acyclic → (mapBifunctor M K F c).Acyclic

/-- Applying a bifunctor to an acyclic complex and a complex K-flat for that bifunctor gives an
acyclic total complex. -/
lemma IsKFlatFor.acyclic_mapBifunctor {K : HomologicalComplex C₂ c₂}
    {F : C₁ ⥤ C₂ ⥤ D} [TotalComplexShape c₁ c₂ c] [DecidableEq J]
    [F.PreservesZeroMorphisms]
    [∀ X : C₁, (F.obj X).PreservesZeroMorphisms] (hK : K.IsKFlatFor F c₁ c)
    {M : HomologicalComplex C₁ c₁} [HasMapBifunctor M K F c]
    (hM : M.Acyclic) : (mapBifunctor M K F c).Acyclic := sorry

/-- Relative K-flatness is exactly preservation of acyclicity by the associated totalized
bifunctor. -/
theorem isKFlatFor_iff (K : HomologicalComplex C₂ c₂) (F : C₁ ⥤ C₂ ⥤ D)
    (c₁ : ComplexShape I₁) (c : ComplexShape J)
    [TotalComplexShape c₁ c₂ c] [DecidableEq J]
    [F.PreservesZeroMorphisms] [∀ X : C₁, (F.obj X).PreservesZeroMorphisms] :
    K.IsKFlatFor F c₁ c ↔
      ∀ ⦃M : HomologicalComplex C₁ c₁⦄ [HasMapBifunctor M K F c],
        M.Acyclic → (mapBifunctor M K F c).Acyclic := sorry

end HomologicalComplex
