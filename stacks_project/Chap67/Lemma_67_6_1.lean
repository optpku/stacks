module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-! Representable universally open morphisms of algebraic spaces. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.6.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is universally open in the
sense of Section 67.3 if and only if for every morphism of algebraic spaces
`Z ⟶ Y` the morphism of topological spaces `|Z ×_Y X| ⟶ |Z|` is open. -/
@[stacks 03Z1] #check (AlgebraicGeometry.AlgebraicSpace.universallyOpen_presheaf_iff_universallyOpen :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f),
    (over (@AlgebraicGeometry.UniversallyOpen : MorphismProperty Scheme.{u})).presheaf f ↔
      UniversallyOpen f)

end AlgebraicGeometry.AlgebraicSpace
