/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.PredecessorLimit

/-!
# Acyclic limits of well-ordered inverse systems

This file gives the homological consequence of the generic predecessor-limit comparison.  Its
epimorphism hypothesis is categorical; for `AddCommGrpCat` it is equivalent to surjectivity of
the underlying group homomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe v u

namespace CochainComplex

/-- A well-order-indexed inverse limit of acyclic cochain complexes of abelian groups is acyclic
when every predecessor-limit comparison is an epimorphism. -/
@[stacks 0AAT "acyclic inverse limits over well-orders"]
theorem limitAcyclic_of_predecessorComparison_epi
    {J : Type u} [LinearOrder J] [WellFoundedLT J] [UnivLE.{u, v}]
    (K : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℤ)
    (hacyclic : ∀ β : J, (K.obj (op β)).Acyclic)
    (hcomparison : ∀ β : J, Epi (K.predecessorLimitComparison β)) :
    (limit K).Acyclic := sorry

end CochainComplex
