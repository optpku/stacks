/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import ReasLib.Algebra.Homology.DerivedCategory.Ext.Functor
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Inclusion
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pseudo-coherence and filtered colimits of derived Ext

For an `m`-pseudo-coherent derived module, the functors `Ext^n(K, -)` commute
with filtered colimits below the boundary degree `-m`, while the comparison is
injective at the boundary.  For bounded-above objects these conditions also
characterize `m`-pseudo-coherence.

@stack 0G8W
@stack 0G8X
-/

noncomputable section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [Ring R]

/-- The filtered-colimit Ext condition: comparison is invertible below degree `-m` and
monic in degree `-m`. -/
@[stacks 0G8X "filtered-colimit Ext criterion"]
abbrev FilteredColimitExtCriterion
    (K : DerivedCategory (ModuleCat R)) (m : ℤ) : Prop :=
  ∀ ⦃J : Type v⦄ [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat R),
      (∀ n : ℤ, n < -m →
        IsIso (colimit.post F (Ext.addCommGrpFunctor K n))) ∧
      Mono (colimit.post F (Ext.addCommGrpFunctor K (-m)))

namespace IsMPseudoCoherent

/-- Lemma 15.66.1 (1): below degree `-m`, derived Ext from an
`m`-pseudo-coherent object commutes with filtered colimits. -/
@[stacks 0G8W "Lemma 15.66.1 (1)"]
theorem extFilteredColimitComparison_isIso
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {K : DerivedCategory (ModuleCat R)} {m n : ℤ}
    (hK : DerivedCategory.IsMPseudoCoherent K m) (F : J ⥤ ModuleCat R)
    (hn : n < -m) :
    IsIso (colimit.post F (Ext.addCommGrpFunctor K n)) := sorry
-- Proof strategy: choose the bounded finite-free approximation supplied by `hK`, identify Ext
-- below `-m` with Ext from that approximation, and use exactness of filtered colimits together
-- with finite freeness of every term to show that the comparison is invertible.

/-- Lemma 15.66.1 (2): in degree `-m`, the filtered-colimit comparison for
derived Ext from an `m`-pseudo-coherent object is monic. -/
@[stacks 0G8W "Lemma 15.66.1 (2)"]
theorem extFilteredColimitComparison_mono
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {K : DerivedCategory (ModuleCat R)} {m : ℤ}
    (hK : DerivedCategory.IsMPseudoCoherent K m) (F : J ⥤ ModuleCat R) :
    Mono (colimit.post F (Ext.addCommGrpFunctor K (-m))) := sorry
-- Proof strategy: use the same finite-free approximation as in the strict inequality case; the
-- long exact Ext sequence identifies the boundary comparison with a subobject of the comparison
-- for the approximation, which is invertible because filtered colimits are exact.

/-- An `m`-pseudo-coherent object satisfies the filtered-colimit Ext criterion. -/
@[stacks 0G8W "filtered-colimit Ext criterion for pseudo-coherent objects"]
theorem filteredColimitExtCriterion
    {K : DerivedCategory (ModuleCat R)} {m : ℤ}
    (hK : DerivedCategory.IsMPseudoCoherent K m) :
    DerivedCategory.FilteredColimitExtCriterion K m := sorry
-- Proof strategy: for each filtered module diagram, combine
-- `extFilteredColimitComparison_isIso` in every degree below `-m` with
-- `extFilteredColimitComparison_mono` in degree `-m`.

end IsMPseudoCoherent

namespace Minus

/-- The filtered-colimit Ext criterion for an object of the bounded-above derived category. -/
@[stacks 0G8X "bounded-above filtered-colimit Ext criterion"]
abbrev FilteredColimitExtCriterion
    (K : DerivedCategory.Minus (ModuleCat R)) (m : ℤ) : Prop :=
  DerivedCategory.FilteredColimitExtCriterion K.obj m

/-- Lemma 15.66.2: a bounded-above derived module is `m`-pseudo-coherent exactly when its
derived Ext functors satisfy the filtered-colimit comparison criterion. -/
@[stacks 0G8X "Lemma 15.66.2"]
theorem isMPseudoCoherent_iff_filteredColimitExt
    (K : DerivedCategory.Minus (ModuleCat R)) (m : ℤ) :
    DerivedCategory.IsMPseudoCoherent K.obj m ↔
      Minus.FilteredColimitExtCriterion K m := sorry
-- Proof strategy: the forward implication is `IsMPseudoCoherent.filteredColimitExtCriterion`.
-- Conversely, induct on the largest degree with nonzero homology; the boundary monomorphism
-- makes the top homology finite, a finite-free cover lowers the bound, and the strict-degree
-- comparison hypotheses pass to the cone through the long exact Ext sequence.

end Minus

end CategoryTheory.DerivedCategory
