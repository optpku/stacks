module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Noetherian
import StacksCheckRecall

/-!
# Lemma 29.35.6

Over a locally Noetherian base, unramified and G-unramified morphisms coincide.

@stack 04EV
-/

@[expose] public section

universe u

/- Lemma 29.35.6: A morphism to a locally Noetherian scheme is unramified if and only if it is
G-unramified. -/
@[stacks 04EV] #check
  (AlgebraicGeometry.Unramified.iff_gUnramified :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsLocallyNoetherian S],
      AlgebraicGeometry.Unramified f ↔ AlgebraicGeometry.GUnramified f)
