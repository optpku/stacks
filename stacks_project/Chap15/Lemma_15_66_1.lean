/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.FilteredColimitExt
import StacksCheckRecall

@[expose] public section

/-!
# Filtered colimits of derived Ext

Lemma 15.66.1 is owned by the reusable pseudo-coherent filtered-colimit API.

@stack 0G8W
-/

open CategoryTheory CategoryTheory.Limits

universe u v

/- The additive-group-valued derived Ext functor is canonical setup data, not a separate clause of
Lemma 15.66.1. -/
#check @CategoryTheory.DerivedCategory.Ext.addCommGrpFunctor

/- Lemma 15.66.1 (1): below degree `-m`, the canonical filtered-colimit Ext
comparison is invertible. -/
@[stacks 0G8W "Lemma 15.66.1 (1)"]
#check fun {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
    {K : DerivedCategory (ModuleCat R)} {m n : ℤ}
    (hK : K.IsMPseudoCoherent m) (F : J ⥤ ModuleCat R) (hn : n < -m) ↦
  (DerivedCategory.IsMPseudoCoherent.extFilteredColimitComparison_isIso hK F hn :
    IsIso (colimit.post F (DerivedCategory.Ext.addCommGrpFunctor K n)))

/- Lemma 15.66.1 (2): at degree `-m`, the canonical filtered-colimit Ext
comparison is injective. -/
@[stacks 0G8W "Lemma 15.66.1 (2)"]
#check fun {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
    {K : DerivedCategory (ModuleCat R)} {m : ℤ}
    (hK : K.IsMPseudoCoherent m) (F : J ⥤ ModuleCat R) ↦
  (DerivedCategory.IsMPseudoCoherent.extFilteredColimitComparison_mono hK F :
    Mono (colimit.post F (DerivedCategory.Ext.addCommGrpFunctor K (-m))))
