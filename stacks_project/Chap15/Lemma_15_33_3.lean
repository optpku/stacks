/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.Local.Localization

/-!
# Locality of local complete-intersection ring maps

The reusable owner is `RingHom.IsLocalCompleteIntersection.ofLocalizationSpanTarget` in
`ReasLib.RingTheory.CompleteIntersection.Local.Localization`.  This chapter file preserves the
source label and exposes only the recall surface, so downstream imports never need to depend on a
chapter module.

@stack 07D1
-/

@[expose] public section

/- Lemma 15.33.3, tag `07D1`: local complete intersection is local on the
target for principal-open covers. -/
@[stacks 07D1 "local complete-intersection maps on the target"]
#check @RingHom.IsLocalCompleteIntersection.ofLocalizationSpanTarget

/- Lemma 15.33.3, finite principal-open formulation. -/
@[stacks 07D1 "finite principal-open locality for local complete-intersection maps"]
#check @RingHom.IsLocalCompleteIntersection.ofLocalizationFiniteSpanTarget

#check @RingHom.ofLocalizationSpanTarget_iff_finite
