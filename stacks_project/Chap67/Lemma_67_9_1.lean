module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyClosed
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 67.9.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is universally closed in the
sense of Section 67.3 if and only if for every morphism of algebraic spaces
`Z ⟶ Y` the morphism of topological spaces `|Z ×_Y X| ⟶ |Z|` is closed. -/
@[stacks 03XD] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyClosed_presheaf_iff_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
    yoneda.relativelyRepresentable f →
    ((over (@AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u})).presheaf f ↔
      AlgebraicGeometry.AlgebraicSpace.UniversallyClosed f))
