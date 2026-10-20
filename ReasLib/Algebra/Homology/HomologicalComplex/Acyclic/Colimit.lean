/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact colimits of acyclic complexes

This file records the shape-polymorphic fact that an exact colimit of acyclic homological
complexes is acyclic.  It is independent of K-flatness and of any particular coefficient
category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v uI vI w

namespace HomologicalComplex.Acyclic

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
variable {ι : Type w} {c : ComplexShape ι}

/-- Exact colimits preserve acyclicity of homological complexes. -/
@[stacks 06YR "acyclic exact colimits"]
theorem colimit_of_exact (F : I ⥤ HomologicalComplex C c)
    (hF : ∀ i, (F.obj i).Acyclic) :
    (colimit F).Acyclic := sorry

end

end HomologicalComplex.Acyclic
