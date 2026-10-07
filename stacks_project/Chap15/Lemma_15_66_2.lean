module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.FilteredColimitExt
import StacksCheckRecall

@[expose] public section

/-!
# Pseudo-coherence through filtered-colimit Ext

Lemma 15.66.2 is owned by the bounded-above filtered-colimit Ext criterion.

@stack 0G8X
-/

open CategoryTheory CategoryTheory.Limits

universe u v

/- These abbreviations name the two owner-level presentations of the source condition. -/
#check @CategoryTheory.DerivedCategory.FilteredColimitExtCriterion

#check @CategoryTheory.DerivedCategory.Minus.FilteredColimitExtCriterion

/- Lemma 15.66.2: for `K ∈ D^-(R)`, the filtered-colimit Ext criterion is
equivalent to `m`-pseudo-coherence. -/
@[stacks 0G8X "Lemma 15.66.2"]
#check fun {R : Type u} [Ring R]
    (K : DerivedCategory.Minus (ModuleCat R)) (m : ℤ) ↦
  (DerivedCategory.Minus.isMPseudoCoherent_iff_filteredColimitExt K m :
    K.obj.IsMPseudoCoherent m ↔
      ∀ ⦃J : Type v⦄ [SmallCategory J] [IsFiltered J]
        (F : J ⥤ ModuleCat R),
          (∀ n : ℤ, n < -m →
            IsIso (colimit.post F (DerivedCategory.Ext.addCommGrpFunctor K.obj n))) ∧
          Mono (colimit.post F (DerivedCategory.Ext.addCommGrpFunctor K.obj (-m))))
