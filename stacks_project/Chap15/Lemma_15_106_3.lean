module

public import ReasLib.RingTheory.Etale.Weakly.MaximalSubalgebra.Functoriality
import StacksCheckRecall

/-!
# Functoriality of the maximal weakly etale subalgebra

This file records Lemma 15.106.3, Stacks `0CKT`, through the shared functoriality and permanence
API for `Subalgebra.maximalWeaklyEtale`.

@stack 0CKT
-/

@[expose] public section

-- Lemma 15.106.3 (1): algebra maps induce maps on maximal weakly etale subalgebras.
@[stacks 0CKT "Lemma 15.106.3 (1), induced map"]
#check @Subalgebra.maximalWeaklyEtale.map

@[stacks 0CKT "Lemma 15.106.3 (1), functor"]
#check @Subalgebra.maximalWeaklyEtale.functor

-- Lemma 15.106.3 (2): an injective map identifies the source owner with the appropriate comap.
@[stacks 0CKT "Lemma 15.106.3 (2)"]
#check @Subalgebra.maximalWeaklyEtale.comap_of_injective

-- Lemma 15.106.3 (3): the owner functor preserves filtered colimits.
@[stacks 0CKT "Lemma 15.106.3 (3)"]
#check @Subalgebra.maximalWeaklyEtale.preservesFilteredColimits

#check @Subalgebra.maximalWeaklyEtale.eq_sSup_of_directed

-- Lemma 15.106.3 (4): passing to the reduction does not change the owner.
@[stacks 0CKT "Lemma 15.106.3 (4), reduction map"]
#check @Subalgebra.maximalWeaklyEtale.reductionMap

@[stacks 0CKT "Lemma 15.106.3 (4), bijectivity"]
#check @Subalgebra.maximalWeaklyEtale.reductionMap_bijective

-- Lemma 15.106.3 (5): the construction commutes with finite products.
@[stacks 0CKT "Lemma 15.106.3 (5)"]
#check @Subalgebra.maximalWeaklyEtale.pi

-- Lemma 15.106.3 (6): trivial ambient idempotents force the owner to be a field.
@[stacks 0CKT "Lemma 15.106.3 (6)"]
#check @Subalgebra.maximalWeaklyEtale.isField_of_idempotents

-- Lemma 15.106.3 (7): that field is a separable algebraic extension.
@[stacks 0CKT "Lemma 15.106.3 (7), separability"]
#check @Subalgebra.maximalWeaklyEtale.isSeparable_of_idempotents

@[stacks 0CKT "Lemma 15.106.3 (7), algebraicity"]
#check @Subalgebra.maximalWeaklyEtale.isAlgebraic_of_idempotents
