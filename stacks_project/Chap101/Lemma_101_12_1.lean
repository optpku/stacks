/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_7_2_Submersive
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Definition_101_12_2_Submersive

/-!
# Representable universally submersive morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is universally
submersive in the sense of scheme-slice tests of algebraic spaces if and only if
every algebraic-stack base change induces a submersive map on underlying point
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- For every morphism of algebraic stacks `Z ⟶ Y`, the 2-fibre-product
projection `Z ×_Y X ⟶ Z` induces a submersive map of underlying point spaces. -/
def isSubmersiveAfterBaseChange {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    AlgebraicStack.Submersive (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- Being submersive after every algebraic-stack base change means each chosen
2-fibre-product projection `Z ×_Y X ⟶ Z` is a submersive morphism of algebraic
stacks. -/
theorem isSubmersiveAfterBaseChange_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    isSubmersiveAfterBaseChange f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        AlgebraicStack.Submersive (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Submersiveness after algebraic-stack base change is the stack-level
universally submersive property. -/
theorem isSubmersiveAfterBaseChange_iff_universallySubmersive {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    isSubmersiveAfterBaseChange f ↔ AlgebraicStack.UniversallySubmersive f :=
  sorry

/-- Lemma 101.12.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` is universally submersive as in
Properties of Stacks, Section 100.3 if and only if for every morphism of
algebraic stacks `Z ⟶ Y` the morphism of topological spaces `|Z ×_Y X| ⟶ |Z|`
is submersive. -/
@[stacks 0CHX]
theorem has_universallySubmersive_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversallySubmersive S) f ↔
      isSubmersiveAfterBaseChange f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
