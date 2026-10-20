module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import stacks_project.Chap108.Lemma_108_4_2_LocallyOfFinitePresentation

/-!
# Smooth morphisms at the Hom-universe of the stack of coherent sheaves
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

universe u

/- Lemma 108.8.5: smoothness uses a smooth surjective presentation of the morphism. -/
#check (CohStack.Hom.Smooth :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)},
    (X ⟶ Y) → Prop)
