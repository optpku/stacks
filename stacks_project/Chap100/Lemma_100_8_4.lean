module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Monomorphism
import StacksCheckRecall

/-!
# Characterizations of monomorphisms of algebraic stacks

Monomorphisms of algebraic stacks are characterized by full faithfulness,
their relative diagonal, and a covering by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 100.8.4: a morphism of algebraic stacks is a monomorphism if and
only if it is fully faithful. -/
@[stacks 04ZZ] #check
  (AlgebraicGeometry.Groupoids.Hom.Mono.iff_fullyFaithful :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      Mono f ↔ Nonempty (toBasedFunctor f).FullyFaithful)

/- Lemma 100.8.4: a morphism of algebraic stacks is a monomorphism if and
only if its canonical relative diagonal is an equivalence over the base. -/
@[stacks 04ZZ] #check
  (AlgebraicGeometry.Groupoids.Hom.Mono.iff_diagonal_isEquivalence :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      Mono f ↔
        BasedFunctor.IsEquivalence
          (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1} f)))

/- Lemma 100.8.4: a morphism of algebraic stacks is a monomorphism if and
only if it becomes a monomorphism of algebraic spaces after a surjective,
flat, locally of finite presentation algebraic-space covering. -/
@[stacks 04ZZ] #check
  (AlgebraicGeometry.Groupoids.Hom.Mono.iff_exists_covering_mono :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      Mono f ↔
        ∃ (W : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y),
          Surjective g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
            ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
              RepresentsTwoFibreProductOnSpace f g V W v ∧
                CategoryTheory.Mono v)

end AlgebraicGeometry.Groupoids.Hom
