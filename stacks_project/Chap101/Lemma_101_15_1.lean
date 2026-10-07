module

public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Lemma_101_15_1_Homeomorph

/-!
# Representable universal homeomorphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is a universal
homeomorphism in the sense of scheme-slice tests of algebraic spaces if and only
if every algebraic-stack base change induces a homeomorphism on underlying point
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- For every morphism of algebraic stacks `Z ⟶ Y`, the 2-fibre-product
projection `Z ×_Y X ⟶ Z` induces a homeomorphism of underlying point spaces. -/
def isHomeomorphAfterBaseChange {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    AlgebraicStack.pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- Being a homeomorphism after every algebraic-stack base change means each chosen
2-fibre-product projection `Z ×_Y X ⟶ Z` induces a homeomorphism of underlying
point spaces. -/
theorem isHomeomorphAfterBaseChange_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    isHomeomorphAfterBaseChange f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        AlgebraicStack.pointsIsHomeomorph
          (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Lemma 101.15.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` is a universal homeomorphism as in
Properties of Stacks, Section 100.3 if and only if for every morphism of
algebraic stacks `Z ⟶ Y` the map of topological spaces `|Z ×_Y X| ⟶ |Z|` is a
homeomorphism. Here `|Z ×_Y X| ⟶ |Z|` is `Points.map` of `TwoFibreProduct.snd`. -/
@[stacks 0CI6]
theorem has_universalHomeomorphism_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversalHomeomorphism S) f ↔
      isHomeomorphAfterBaseChange f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
