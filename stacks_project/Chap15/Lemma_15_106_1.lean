module

public import ReasLib.RingTheory.Etale.Weakly.Field.Consequences
public import ReasLib.RingTheory.Etale.Weakly.AbsolutelyFlat
import StacksCheckRecall

/-!
# Weakly etale algebras over fields

This file records the eight atomic consequences in Lemma 15.106.1, Stacks `0CKR`, through their
canonical ReasLib owners.

@stack 0CKR
-/

@[expose] public section

-- Lemma 15.106.1 (1): a weakly etale algebra over a field is reduced.
@[stacks 0CKR "Lemma 15.106.1 (1)"]
#check @Algebra.WeaklyEtale.isReduced

-- Lemma 15.106.1 (2): it is integral over the base field.
@[stacks 0CKR "Lemma 15.106.1 (2)"]
#check @Algebra.WeaklyEtale.isIntegral

-- Lemma 15.106.1 (3): its finitely generated subalgebras are finite products of finite separable
-- extensions.
@[stacks 0CKR "Lemma 15.106.1 (3)"]
#check @Algebra.WeaklyEtale.exists_algEquiv_prod_of_fg_subalgebra

-- Lemma 15.106.1 (4): the field criterion is the absence of nontrivial idempotents.
@[stacks 0CKR "Lemma 15.106.1 (4)"]
#check @Algebra.WeaklyEtale.isField_iff_idempotents

-- Lemma 15.106.1 (5): in the field case the extension is separable algebraic.
@[stacks 0CKR "Lemma 15.106.1 (5)"]
#check @Algebra.WeaklyEtale.isSeparable_of_isField

-- Lemma 15.106.1 (6): subalgebras remain weakly etale.
@[stacks 0CKR "Lemma 15.106.1 (6)"]
#check @Algebra.WeaklyEtale.subalgebra

-- Lemma 15.106.1 (7): quotient algebras remain weakly etale.
@[stacks 0CKR "Lemma 15.106.1 (7)"]
#check @Algebra.WeaklyEtale.quotient

-- Lemma 15.106.1 (8): tensor products remain weakly etale.
@[stacks 0CKR "Lemma 15.106.1 (8)"]
#check @Algebra.WeaklyEtale.tensorProduct
