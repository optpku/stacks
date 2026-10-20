/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.RingTheory.RingHom.Perfect.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect ring maps from local complete intersections

The local-complete-intersection hypothesis and the perfect-ring-map conclusion are both properties
of the ring homomorphism.  This leaf owns their reusable implication; a chapter file only needs to
recall the resulting theorem or instance.

@stack 07EN
-/

@[expose] public section

universe u v

namespace RingHom

namespace IsLocalCompleteIntersection

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Lemma 15.83.6 (Stacks `07EN`): a local complete-intersection homomorphism is perfect. -/
@[stacks 07EN "local complete-intersection homomorphisms are perfect"]
theorem isPerfectRingMap {f : A →+* B} (h : f.IsLocalCompleteIntersection) :
    f.IsPerfectRingMap := sorry
/- Proof strategy: extract the finite polynomial presentation with Koszul kernel from `h`; locally
resolve that kernel by the Koszul complex, obtain a finite projective resolution of the quotient,
and apply `RingHom.isPerfectRingMap_iff_hasPerfectPolynomialPresentation`. -/

/-- A local complete-intersection hypothesis supplies the canonical perfect-ring-map instance. -/
@[stacks 07EN "perfect instance of a local complete-intersection homomorphism"]
instance instIsPerfectRingMap {f : A →+* B}
    [h : f.IsLocalCompleteIntersection] : f.IsPerfectRingMap := sorry
/- Proof strategy: apply `h.isPerfectRingMap`; this instance only exposes the canonical property
to typeclass search and introduces no independent construction. -/

end IsLocalCompleteIntersection

end RingHom
