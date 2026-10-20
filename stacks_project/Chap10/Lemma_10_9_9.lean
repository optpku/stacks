/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Colimit
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.9.9: the localization `LocalizedModule S M` is the colimit of the diagram of
principal localizations `LocalizedModule.Away s M`, indexed by `S` with the divisibility order.

The reusable owner is `LocalizedModule.Away`: `divisibilityDiagram` and `divisibilityCocone` give
the concrete diagram and cocone, `mapOfDvd_apply_mk_pow` records the source denominator formula,
and `divisibilityCocone_isColimit` with its `fac` theorem exposes the universal property. The old
chapter proof and its private unit/transport helpers are not part of the public API.

@stack 00CR
-/
@[stacks 00CR "principal localization transition map"]
#check @LocalizedModule.Away.divisibilityMap

@[stacks 00CR "principal localization power-denominator formula"]
#check @LocalizedModule.Away.mapOfDvd_apply_mk_pow

@[stacks 00CR "principal localization diagram"]
#check @LocalizedModule.Away.divisibilityDiagram

@[stacks 00CR "principal localization cocone"]
#check @LocalizedModule.Away.divisibilityCocone

@[stacks 00CR "principal localization universal property"]
#check @LocalizedModule.Away.divisibilityCocone_existsUniqueDesc

@[stacks 00CR "principal localization colimit"]
#check @LocalizedModule.Away.divisibilityCocone_isColimit

@[stacks 00CR "principal localization colimit factorization"]
#check @LocalizedModule.Away.divisibilityCocone_isColimit_fac
