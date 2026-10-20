module

public import ReasLib.RingTheory.Normal.Nagata.EssentialFiniteness
import StacksCheckRecall

@[expose] public section

/-!
# Localizations of Nagata Rings

@stack 032U

The localization permanence theorem is a neutral ReasLib operation, rather
than a Chapter-owned proof implementation.
-/

-- Lemma 10.162.6, tag `032U`: a localization of a Nagata ring is Nagata.
@[stacks 032U]
#check @NagataRing.of_isLocalization
