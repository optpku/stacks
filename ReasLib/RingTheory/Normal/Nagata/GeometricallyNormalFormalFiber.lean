/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FormalFiber.Geometric.Normal
public import ReasLib.RingTheory.Normal.Nagata.FormalFiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Nagata rings from geometrically normal formal fibers

Geometric normality of every formal fiber implies the Nagata property for a Noetherian local
ring.

@stack 0C2E
-/

@[expose] public section

universe u

namespace NagataRing

/-- Lemma 15.109.8 (1): a Noetherian local ring with geometrically normal formal fibers is
Nagata. -/
@[stacks 0C2E "Lemma 15.109.8 (1)"]
theorem of_geometricallyNormalFormalFibers
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : FieldAlgebraProperty.geometricallyNormal.HoldsOnFormalFibers A) :
    NagataRing A := sorry
-- Proof strategy: geometric normality implies geometric reducedness for every formal fiber;
-- apply the canonical constructor `NagataRing.of_geometricallyReducedFormalFibers`.

end NagataRing
