/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed
public import ReasLib.RingTheory.RingHom.IndFiniteFree

@[expose] public section

/-!
# Free absolutely integrally closed extensions

The existence statement is kept at the ring-map level: the extension map is
injective, its target is free over the base, and the map is an ind-finite-free
map.  This makes the construction usable without exposing the internal
root-adjoining stages.

@stack 0DCR
-/

universe u v

namespace IsAbsolutelyIntegrallyClosed

/- The textbook construction chooses a carrier in the base universe.  The
shared theorem allows `Type (max u v)`, matching the universe-polymorphic
existence APIs in ReasLib; choosing `v = 0` recovers the source-level carrier
up to universe normalization, while downstream extensions can use a larger
ambient universe without rebuilding the root-adjoining stages. -/
/-- Lemma 15.14.6, tag `0DCR`: every commutative ring admits an injective
free ind-finite-free extension that is absolutely integrally closed. -/
@[stacks 0DCR "free absolutely integrally closed extension"]
theorem exists_freeExtension (A : Type u) [CommRing A] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra A B),
      Function.Injective (algebraMap A B) ∧
      Module.Free A B ∧
      (algebraMap A B).IndFiniteFree ∧
      IsAbsolutelyIntegrallyClosed B := sorry
-- Proof strategy: build directed finite root-adjoining stages with `Polynomial.Monic` and
-- `AdjoinRoot`, pass to their colimit via `MorphismProperty.ind`, and iterate until
-- `IsAbsolutelyIntegrallyClosed.of_exists_root` applies.

end IsAbsolutelyIntegrallyClosed
