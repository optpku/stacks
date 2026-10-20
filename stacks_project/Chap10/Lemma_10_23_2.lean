/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cover
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
public import Mathlib.RingTheory.RingHom.FinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.23.2

@stack 00EO

The eight assertions are existing locality theorems in Mathlib and ReasLib.  This file records
their source correspondence without introducing chapter-level aliases.
-/

/- Lemma 10.23.2 (1): a module which vanishes on a spanning family of principal opens
vanishes globally. -/
@[stacks 00EO "(1), zero module"]
#check @Module.subsingleton_of_localizationSpan

/- Lemma 10.23.2 (2): finite generation is local on a spanning family of principal opens. -/
@[stacks 00EO "(2), finite module"]
#check @Module.Finite.of_localizationSpan

/- Lemma 10.23.2 (3): finite presentation is local on a spanning family of principal opens. -/
@[stacks 00EO "(3), finitely presented module"]
#check @Module.FinitePresentation.of_localizationSpan

/- Lemma 10.23.2 (4): a linear map which is an isomorphism on a spanning family of principal
opens is an isomorphism globally.  The canonical criterion is stated as bijectivity. -/
@[stacks 00EO "(4), module isomorphism"]
#check @bijective_of_localized_span

/- Lemma 10.23.2 (5): short exactness is local on a spanning family of principal opens. -/
@[stacks 00EO "(5), short exact sequence"]
#check @CategoryTheory.ShortComplex.ShortExact.of_localizationSpan

/- Lemma 10.23.2 (6): the Noetherian property is local on a spanning family of principal
opens. -/
@[stacks 00EO "(6), Noetherian ring"]
#check @AlgebraicGeometry.isNoetherianRing_of_away

/- Lemma 10.23.2 (7): finite type is local on the source for a spanning family of principal
opens. -/
@[stacks 00EO "(7), finite type algebra"]
#check @Algebra.FiniteType.of_span_eq_top_source

/- Lemma 10.23.2 (8): finite presentation is local on the source for a spanning family of
principal opens. -/
@[stacks 00EO "(8), finitely presented algebra"]
#check @RingHom.finitePresentation_isLocal.ofLocalizationSpan
