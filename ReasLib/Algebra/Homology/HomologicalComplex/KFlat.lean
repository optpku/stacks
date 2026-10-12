/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat homological complexes

@stack 06XZ

This file owns K-flatness for complexes in an arbitrary monoidal preadditive category.  It is the
monoidal specialization of bifunctor-relative K-flatness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]
variable {I : Type w} [AddMonoid I] [DecidableEq I]
  {c : ComplexShape I} [c.TensorSigns]

/-- A homological complex is K-flat if totalized tensoring with it preserves acyclic complexes. -/
@[stacks 06XZ "homological-complex form"]
def IsKFlat (K : HomologicalComplex C c) : Prop :=
  K.IsKFlatFor (curriedTensor C) c c

/-- Tensoring an acyclic complex with a K-flat complex gives an acyclic complex. -/
lemma IsKFlat.acyclic_tensorObj {K : HomologicalComplex C c} (hK : K.IsKFlat)
    {M : HomologicalComplex C c} [HasTensor M K] (hM : M.Acyclic) :
    (tensorObj M K).Acyclic := sorry

/-- A homological complex is K-flat exactly when totalized tensoring with it preserves acyclic
complexes. -/
theorem isKFlat_iff (K : HomologicalComplex C c) :
    K.IsKFlat ↔
      ∀ ⦃M : HomologicalComplex C c⦄ [HasTensor M K],
        M.Acyclic → (tensorObj M K).Acyclic := sorry

end HomologicalComplex
