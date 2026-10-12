/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 44.2.3: a closed immersion induces a closed immersion between the representing
schemes of the corresponding degree-`d` Hilbert functors. -/
@[stacks 0B97] #check
  (AlgebraicGeometry.Hilbert.exists_closedImmersion_representation :
    ∀ {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y) [IsClosedImmersion i.left]
      (d : ℕ) {HY : Over S} (RY : (AlgebraicGeometry.Hilbert.functor Y d).RepresentableBy HY),
      ∃ (HX : Over S) (RX : (AlgebraicGeometry.Hilbert.functor X d).RepresentableBy HX),
        IsClosedImmersion
          (RX.map RY (AlgebraicGeometry.Hilbert.closedImmersionMap i d)).left)
