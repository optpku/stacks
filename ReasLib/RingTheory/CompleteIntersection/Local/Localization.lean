/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalProperties.Basic
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Target-locality of local complete-intersection ring maps

This leaf owns the principal-open descent API for the intrinsic
`RingHom.IsLocalCompleteIntersection` predicate.  The source-facing chapter only recalls these
declarations; no chapter module is needed by downstream users.

@stack 07D1
-/

namespace RingHom

namespace IsLocalCompleteIntersection

/-- Local complete-intersection ring maps are local on the target for
principal-open covers. -/
@[stacks 07D1 "local complete-intersection maps on the target"]
theorem ofLocalizationSpanTarget :
    OfLocalizationSpanTarget IsLocalCompleteIntersection := sorry

/-- Finite principal-open form of target-locality for local complete-intersection ring maps. -/
@[stacks 07D1 "finite principal-open locality for local complete-intersection maps"]
theorem ofLocalizationFiniteSpanTarget :
    OfLocalizationFiniteSpanTarget IsLocalCompleteIntersection := sorry

/-- Local complete-intersection maps remain local complete intersections after principal
localization of the source and target. -/
@[stacks 07D1 "localization preservation for local complete-intersection maps"]
theorem localizationAwayPreserves :
    RingHom.LocalizationAwayPreserves @IsLocalCompleteIntersection := sorry

/-- A local complete-intersection map is detected after principal localization of its source. -/
@[stacks 07D1 "source-locality for local complete-intersection maps"]
theorem ofLocalizationSpan :
    RingHom.OfLocalizationSpan @IsLocalCompleteIntersection := sorry

/-- The complete local-property package for local complete-intersection ring maps. -/
@[stacks 07D1 "local-property bundle for local complete-intersection maps"]
theorem propertyIsLocal :
    RingHom.PropertyIsLocal @IsLocalCompleteIntersection := sorry

end IsLocalCompleteIntersection

end RingHom
