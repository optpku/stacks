/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.Away.Idempotent.FinitePresentation
import StacksCheckRecall

/-!
# Idempotent localizations from finite presentation

@stack 00U8
-/

@[expose] public section

/- Lemma 10.143.9: a surjective, flat, finitely presented ring map is localization away from an
idempotent of its source. -/
@[stacks 00U8 "finite-presentation idempotent localization owner"]
#check @Algebra.FinitePresentation.exists_idempotent_localizationAway_of_surjective_of_flat

@[stacks 00U8 "map-level idempotent localization"]
#check @RingHom.IsIdempotentLocalization.of_surjective

@[stacks 00U8 "away localization constructor"]
#check @IsLocalization.away_of_isIdempotentElem

@[stacks 00U8 "finitely-generated idempotent criterion"]
#check @Ideal.isIdempotentElem_iff_of_fg
