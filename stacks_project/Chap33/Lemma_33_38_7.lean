/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.FiniteDescent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/-!
# Lemma 33.38.7 canonical check

Finite descent of invertible modules across a discrete open complement is
owned by the scheme-morphism Picard API.
-/

/- Lemma 33.38.7: for a finite morphism that is an isomorphism over an open
subset with discrete complement, every invertible module on the source is the
pullback of an invertible module on the target. -/
@[stacks 0C0T] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteDescent.existsInvertiblePullback :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
      (_ :
        ∃ (V : Y.Opens) (_ : IsIso (f ∣_ V)),
          IsDiscrete ((V : Set Y)ᶜ)),
      ∀ (L : X.Modules) [Scheme.Modules.Invertible L],
        ∃ (N : Y.Modules) (_ : Scheme.Modules.Invertible N),
          Nonempty (L ≅ ((Scheme.Modules.pullback f).obj N)))
