module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Derived

@[expose] public section

/-!
# Lemma 15.96.4

@stack 0F7R
-/

/-! # The derived Berthelot-Ogus eta functor -/

/- Lemma 15.96.4, tag `0F7R`: the Berthelot-Ogus eta construction descends to an additive
endofunctor of the derived category and is computed, on objects and morphisms represented by
termwise `f`-torsion-free complexes, by the underived eta functor. -/
@[stacks 0F7R "derived Berthelot-Ogus eta functor"]
#check @CochainComplex.BerthelotOgus.Int.Derived.functor

@[stacks 0F7R "derived eta comparison"]
#check @CochainComplex.BerthelotOgus.Int.Derived.comparison

@[stacks 0F7R "derived eta morphism computation"]
#check @CochainComplex.BerthelotOgus.Int.Derived.map_toDerived
