/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Formal
public import ReasLib.RingTheory.Catenary.Universally

@[expose] public section

/-!
# Universal catenarity of formally catenary rings

Formal catenarity is the local completion criterion; universal catenarity is
the construction-facing property consumed by finite-type algebras. This leaf
owns the canonical typeclass bridge between them.
@stack 0AW5
-/

universe u v

namespace IsFormallyCatenaryRing

/-- Lemma 15.110.4 (current Stacks numbering: Lemma 15.111.4, tag `0AW5`):
a formally catenary Noetherian local ring is universally catenary. The local
and Noetherian structures are inherited from `IsFormallyCatenaryRing`. -/
@[stacks 0AW5 "formal catenarity implies universal catenarity"]
instance toUniversallyCatenaryRing
    {A : Type u} [CommRing A] [IsFormallyCatenaryRing A] :
    UniversallyCatenaryRing.{u, v} A := sorry
-- Proof strategy: apply the formal-catenarity criterion to every finite-type `A`-algebra;
-- equidimensional completed minimal-prime quotients give the catenary chain condition required
-- by the canonical `UniversallyCatenaryRing` constructor.

end IsFormallyCatenaryRing

section

variable (A : Type u) [CommRing A] [IsFormallyCatenaryRing A]

#synth IsLocalRing A
#synth IsNoetherianRing A
#synth UniversallyCatenaryRing.{u, v} A

end
