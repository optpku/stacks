/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Formal.Ratliff
public import ReasLib.RingTheory.Catenary.Formal.ToUniversal
public import ReasLib.RingTheory.FormalFiber.Geometric.Normal
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.Henselian.Noetherian
public import ReasLib.RingTheory.LocalRing.Unibranch.Henselization

@[expose] public section

/-!
# Geometrically normal formal fibers and catenarity

This leaf owns the catenarity consequences of geometrically normal formal fibers.
The formal-catenarity statements are exposed separately so later developments can
reuse the intermediate property without committing to Ratliff's equivalence.

@stack 0C2F
-/

universe u v w

namespace IsFormallyCatenaryRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-- Formal catenarity of any chosen Henselization whose Noetherian local base has
geometrically normal formal fibers. This is the reusable intermediate form of
Lemma 15.110.6. -/
@[stacks 0C2F "formal catenarity after Henselization"]
theorem of_henselization
    (hgeom :
      (FieldAlgebraProperty.geometricallyNormal).HoldsOnFormalFibers A) :
    IsFormallyCatenaryRing Ah := sorry
-- Proof strategy: transfer geometrically normal formal fibers from `A` to its henselization;
-- normal fibers are equidimensional, so the completed minimal-prime quotients satisfy
-- `IsFormallyCatenaryRing.iff`.

end IsFormallyCatenaryRing

namespace IsFormallyCatenaryRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Formal catenarity of a unibranch Noetherian local ring with geometrically
normal formal fibers. This bridge is useful independently of the universal-
catenarity conclusion. -/
@[stacks 0C2F "formal catenarity of a unibranch ring"]
theorem of_unibranch [IsUnibranch A]
    (hgeom :
      (FieldAlgebraProperty.geometricallyNormal).HoldsOnFormalFibers A) :
    IsFormallyCatenaryRing A := sorry
-- Proof strategy: pass to the henselization using `of_henselization`; unibranchness identifies
-- its unique minimal branch, and formal catenarity descends through the faithfully flat local map.

end IsFormallyCatenaryRing

namespace UniversallyCatenaryRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-- Lemma 15.110.6 (1) (current Stacks numbering: Lemma 15.111.6, tag
`0C2F`): a Henselization of a Noetherian local ring with geometrically normal
formal fibers is universally catenary. -/
@[stacks 0C2F "Lemma 15.110.6 (1), universal catenarity of a Henselization"]
theorem of_henselization
    (hgeom :
      (FieldAlgebraProperty.geometricallyNormal).HoldsOnFormalFibers A) :
    UniversallyCatenaryRing.{v, w} Ah := sorry
-- Proof strategy: obtain `IsFormallyCatenaryRing Ah` from
-- `IsFormallyCatenaryRing.of_henselization hgeom`, then apply its canonical universal-catenary
-- instance.

/-- Lemma 15.110.6 (2) (current Stacks numbering: Lemma 15.111.6, tag
`0C2F`): a unibranch Noetherian local ring with geometrically normal formal
fibers is universally catenary. -/
@[stacks 0C2F "Lemma 15.110.6 (2), universal catenarity of a unibranch ring"]
theorem of_unibranch [IsUnibranch A]
    (hgeom :
      (FieldAlgebraProperty.geometricallyNormal).HoldsOnFormalFibers A) :
    UniversallyCatenaryRing.{u, w} A := sorry
-- Proof strategy: obtain `IsFormallyCatenaryRing A` from
-- `IsFormallyCatenaryRing.of_unibranch hgeom`, then apply the formal-to-universal instance.

end UniversallyCatenaryRing
