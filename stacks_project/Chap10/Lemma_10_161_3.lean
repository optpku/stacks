/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Localizations of N-1 and N-2 Domains

@stack 032G
-/

-- Lemma 10.161.3 (1), tag `032G`: a localization of an `N-1` domain that is a domain is
-- again `N-1`.
@[stacks 032G "(1)"]
#check @IsN1Ring.of_isLocalization

-- Lemma 10.161.3 (2), tag `032G`: a localization of an `N-2` domain that is a domain is
-- again `N-2`.
@[stacks 032G "(2)"]
#check @IsN2Ring.of_isLocalization
