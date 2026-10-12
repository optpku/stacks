/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 40.10.12 (1): for a groupoid scheme whose object scheme is isomorphic to the spectrum
of a characteristic-zero field, local finite type of both endpoint maps implies that the source
map is smooth. -/
@[stacks 04RA] #check
  (AlgebraicGeometry.GroupoidScheme.sourceSmoothOfCharZero :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k] [CharZero k]
      (eU : Spec (CommRingCat.of k) ≅ G.U.left)
      [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left],
      Smooth G.s.left)

/- Lemma 40.10.12 (2): for a groupoid scheme whose object scheme is isomorphic to the spectrum
of a characteristic-zero field, local finite type of both endpoint maps implies that the target
map is smooth. -/
@[stacks 04RA] #check
  (AlgebraicGeometry.GroupoidScheme.targetSmoothOfCharZero :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k] [CharZero k]
      (eU : Spec (CommRingCat.of k) ≅ G.U.left)
      [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left],
      Smooth G.t.left)
