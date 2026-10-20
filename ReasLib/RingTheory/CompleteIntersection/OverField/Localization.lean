/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.OverField
public import ReasLib.RingTheory.KrullDimension.Presentation

@[expose] public section

/-!
# Localization of Complete Intersections over a Field

This leaf records stability of global and local complete intersections under
an arbitrary localization away from one element.  The canonical
`Localization.Away g` instances are consequences of the more reusable
`IsLocalization.Away g Sg` theorems.
-/

universe u v w

namespace IsGlobalCompleteIntersection

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]
variable {Sg : Type w} [CommRing Sg] [Algebra S Sg] [Algebra k Sg] [IsScalarTower k S Sg]

/-- Lemma 10.135.2 (1), tag `00SA`: global complete intersections over a
field are preserved by localization away from one element. -/
@[stacks 00SA "global complete intersections under localization away"]
theorem of_isLocalizationAway (g : S) (hS : IsGlobalCompleteIntersection k S)
    [IsLocalization.Away g Sg] : IsGlobalCompleteIntersection k Sg := sorry

end IsGlobalCompleteIntersection

namespace IsLocalCompleteIntersection

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]
variable {Sg : Type w} [CommRing Sg] [Algebra S Sg] [Algebra k Sg] [IsScalarTower k S Sg]

/-- Lemma 10.135.2 (2), tag `00SA`: local complete intersections over a
field are preserved by localization away from one element. -/
@[stacks 00SA "local complete intersections under localization away"]
theorem of_isLocalizationAway (g : S) (hS : IsLocalCompleteIntersection k S)
    [IsLocalization.Away g Sg] : IsLocalCompleteIntersection k Sg := sorry

end IsLocalCompleteIntersection

namespace IsGlobalCompleteIntersection

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- The canonical localization away from one element of a global complete
intersection over a field is again a global complete intersection. -/
instance instLocalizationAway (g : S)
    [hS : IsGlobalCompleteIntersection k S] :
    IsGlobalCompleteIntersection k (Localization.Away g) := sorry

end IsGlobalCompleteIntersection

namespace IsLocalCompleteIntersection

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- The canonical localization away from one element of a local complete
intersection over a field is again a local complete intersection. -/
instance instLocalizationAway (g : S)
    [hS : IsLocalCompleteIntersection k S] :
    IsLocalCompleteIntersection k (Localization.Away g) := sorry

end IsLocalCompleteIntersection
