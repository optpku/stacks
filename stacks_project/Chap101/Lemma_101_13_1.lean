module

public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Representable universally closed morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is universally
closed in the sense of scheme-slice tests of algebraic spaces if and only if
every algebraic-stack base change induces a closed map on underlying point
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- For every morphism of algebraic stacks `Z ⟶ Y`, the 2-fibre-product
projection `Z ×_Y X ⟶ Z` induces a closed map of underlying point spaces. -/
def isClosedMapAfterBaseChange {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    AlgebraicStack.Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- Being closed after every algebraic-stack base change means each chosen
2-fibre-product projection `Z ×_Y X ⟶ Z` is a closed morphism of algebraic
stacks. -/
theorem isClosedMapAfterBaseChange_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    isClosedMapAfterBaseChange f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        AlgebraicStack.Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Closedness after algebraic-stack base change is the stack-level universally
closed property. -/
theorem isClosedMapAfterBaseChange_iff_universallyClosed {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    isClosedMapAfterBaseChange f ↔ AlgebraicStack.UniversallyClosed f :=
  sorry

/-- Lemma 101.13.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` is universally closed as in
Properties of Stacks, Section 100.3 if and only if for every morphism of
algebraic stacks `Z ⟶ Y` the morphism of topological spaces `|Z ×_Y X| ⟶ |Z|`
is closed. -/
@[stacks 0512]
theorem has_universallyClosed_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversallyClosed S) f ↔ isClosedMapAfterBaseChange f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
