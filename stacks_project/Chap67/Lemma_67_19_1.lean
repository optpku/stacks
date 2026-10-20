module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
import StacksCheckRecall

/-!
# Universally injective representable morphisms of algebraic spaces

A representable morphism of algebraic spaces is universally injective in the
sense of Section 67.3 if and only if it is injective on field-valued points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

/- Lemma 67.19.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is universally injective in the
sense of Section 67.3 if and only if for all fields `K` the map `X(K) → Y(K)` is
injective. -/
@[stacks 03MU] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyInjective_iff_injectiveOnFieldPoints :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
      yoneda.relativelyRepresentable f →
      ((over (@AlgebraicGeometry.UniversallyInjective : MorphismProperty Scheme.{u})).presheaf f ↔
        AlgebraicGeometry.AlgebraicSpace.injectiveOnFieldPoints f))
