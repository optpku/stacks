module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.AutoAssociated.Annihilator
import StacksCheckRecall

/-!
# Annihilators in auto-associated rings

@stack 05GN
-/

@[expose] public section

-- Lemma 15.15.2: every proper finitely generated ideal of an auto-associated ring has nonzero
-- annihilator.
@[stacks 05GN "Lemma 15.15.2"]
#check @IsAutoAssociatedRing.annihilator_ne_bot_of_fg_of_ne_top

@[stacks 05GN "torsion-ideal criterion"]
#check @Ideal.annihilator_ne_bot_of_fg_of_ne_top_of_torsionOf_isIdealOfDefinition
