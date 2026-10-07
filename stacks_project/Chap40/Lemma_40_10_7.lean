module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Composition.Open

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-
Lemma 40.10.7: If the object scheme of a groupoid scheme is the spectrum of a field, then
the image of the composition of an arbitrary family of arrows with an open subscheme of the
arrow scheme is open.
-/
@[stacks 0B7V] #check
  (AlgebraicGeometry.GroupoidScheme.isOpen_range_compOpen :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k],
      (Spec (CommRingCat.of k) ≅ G.U.left) →
        ∀ {Z : Scheme.{u}} (z : Z ⟶ G.R.left) (W : Scheme.Opens G.R.left),
          IsOpen (Set.range (G.compOpen z W).left.base))

end AlgebraicGeometry.GroupoidScheme
