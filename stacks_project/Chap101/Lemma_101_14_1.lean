/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Representable universally injective morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is universally
injective in the sense of scheme-slice tests of algebraic spaces if and only if
every algebraic-stack base change induces an injective map on underlying point
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- For every morphism of algebraic stacks `Z ⟶ Y`, the 2-fibre-product
projection `Z ×_Y X ⟶ Z` induces an injective map of underlying point spaces. -/
def isInjectiveAfterBaseChange {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    Function.Injective
      (AlgebraicStack.Points.map (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

/-- Being injective after every algebraic-stack base change means each chosen
2-fibre-product projection `Z ×_Y X ⟶ Z` induces an injective map of
underlying point spaces. -/
theorem isInjectiveAfterBaseChange_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    isInjectiveAfterBaseChange f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        Function.Injective
          (AlgebraicStack.Points.map (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :=
  sorry

/-- Lemma 101.14.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` is universally injective as in
Properties of Stacks, Section 100.3 if and only if for every morphism of
algebraic stacks `Z ⟶ Y` the map `|Z ×_Y X| ⟶ |Z|` is injective. -/
@[stacks 0CI1]
theorem has_universallyInjective_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversallyInjective S) f ↔
      isInjectiveAfterBaseChange f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
