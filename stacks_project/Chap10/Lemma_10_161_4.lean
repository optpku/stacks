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
# Locality of N-1 and N-2 Conditions

This source-facing file recalls the finite principal-open locality criteria for
Japanese domains.

@stack 032H
-/

-- Lemma 10.161.4 (1), tag `032H`: `N-1` descends from a finite principal-open cover.
@[stacks 032H "(1)"]
#check @IsN1Ring.of_localizationSpan

-- Lemma 10.161.4 (2), tag `032H`: `N-2` descends from a finite principal-open cover.
@[stacks 032H "(2)"]
#check @IsN2Ring.of_localizationSpan
