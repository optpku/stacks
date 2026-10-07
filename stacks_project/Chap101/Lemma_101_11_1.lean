module

public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Lemma_101_27_15_OpenMap

/-!
# Representable universally open morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is universally
open in the sense of scheme-slice tests of algebraic spaces if and only if
every algebraic-stack base change induces an open map on underlying point
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- For every morphism of algebraic stacks `Z ⟶ Y`, the 2-fibre-product
projection `Z ×_Y X ⟶ Z` induces an open map of underlying point spaces. -/
def isOpenMapAfterBaseChange {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    AlgebraicStack.pointsIsOpenMap (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- Being open after every algebraic-stack base change means each chosen
2-fibre-product projection `Z ×_Y X ⟶ Z` induces an open map of underlying
point spaces. -/
theorem isOpenMapAfterBaseChange_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    isOpenMapAfterBaseChange f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        AlgebraicStack.pointsIsOpenMap (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Lemma 101.11.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` is universally open as in
Properties of Stacks, Section 100.3 if and only if for every morphism of
algebraic stacks `Z ⟶ Y` the morphism of topological spaces `|Z ×_Y X| ⟶ |Z|`
is open. -/
@[stacks 06U1]
theorem has_universallyOpen_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversallyOpen S) f ↔ isOpenMapAfterBaseChange f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
