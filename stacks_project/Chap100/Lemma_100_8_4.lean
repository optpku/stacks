/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.«94_9_8_1_Comparison»
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Characterizations of monomorphisms of algebraic stacks

A morphism of algebraic stacks is a monomorphism if and only if it is fully
faithful, if and only if its relative diagonal is an equivalence, if and only
if it becomes a monomorphism of algebraic spaces after one surjective, flat,
locally of finite presentation algebraic-space covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Mono

/-- Lemma 100.8.4 (1): a morphism `f : X ⟶ Y` of algebraic stacks is a
monomorphism if and only if `toBasedFunctor f` is fully faithful. -/
@[stacks 04ZZ]
theorem iff_fullyFaithful {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Mono f ↔ Nonempty (toBasedFunctor f).FullyFaithful :=
  sorry

/-- A monomorphism of algebraic stacks is fully faithful. -/
theorem fullyFaithful {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Mono f] :
    Nonempty (toBasedFunctor f).FullyFaithful :=
  sorry

/-- A fully faithful morphism of algebraic stacks is a monomorphism. -/
theorem of_fullyFaithful {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : Nonempty (toBasedFunctor f).FullyFaithful) : Mono f :=
  sorry

/-- Lemma 100.8.4 (2): a morphism `f : X ⟶ Y` of algebraic stacks is a
monomorphism if and only if `toBasedFunctor (Hom.diagonal f)` is an
equivalence over the base. -/
@[stacks 04ZZ]
theorem iff_diagonal_isEquivalence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Mono f ↔
      BasedFunctor.IsEquivalence
        (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  sorry

/-- The relative diagonal of a monomorphism of algebraic stacks is an
equivalence over the base. -/
instance diagonal_isEquivalence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Mono f] :
    BasedFunctor.IsEquivalence
      (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  sorry

/-- If the relative diagonal of a morphism of algebraic stacks is an
equivalence over the base, then the morphism is a monomorphism. -/
theorem of_diagonal_isEquivalence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : BasedFunctor.IsEquivalence
      (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1} f))) :
    Mono f :=
  sorry

/-- Lemma 100.8.4 (3): a morphism `f : X ⟶ Y` of algebraic stacks is a
monomorphism if and only if there exist an algebraic space `W` and a
surjective, flat, locally of finite presentation morphism
`g : W.toGroupoids ⟶ Y` together with a representing morphism of algebraic
spaces `v : V ⟶ W` for the projection of `X ×_Y W` that is a monomorphism. -/
@[stacks 04ZZ]
theorem iff_exists_covering_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Mono f ↔
      ∃ (W : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y),
        Surjective g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
          ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
            RepresentsTwoFibreProductOnSpace f g V W v ∧
              CategoryTheory.Mono v :=
  sorry

/-- If a morphism of algebraic stacks becomes a monomorphism of algebraic
spaces after one surjective, flat, locally of finite presentation
algebraic-space covering, then it is a monomorphism. -/
theorem of_exists_covering_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : ∃ (W : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y),
      Surjective g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
        ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
          RepresentsTwoFibreProductOnSpace f g V W v ∧
            CategoryTheory.Mono v) :
    Mono f :=
  sorry

end Mono

end AlgebraicGeometry.Groupoids.Hom
