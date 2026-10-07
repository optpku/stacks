module

public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Zariski-local factoring through a morphism of algebraic stacks

A morphism of algebraic spaces factors Zariski locally through a 1-morphism of
algebraic stacks if every point of the source has an open neighbourhood on
which the structure map is 2-isomorphic to a composite landing in the stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion of an open subspace is an open immersion. -/
instance OpenSubspace.instIsOpenImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) : IsOpenImmersion U.ι :=
  U.isOpenImmersion

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `φ : Y ⟶ Z` of algebraic spaces Zariski-locally factors through
a 1-morphism `f : X ⟶ Z.toGroupoids` if every point of `Y` has an open
neighbourhood `W` on which `W.ι ≫ φ` is 2-isomorphic to a composite through
`f`. -/
def zariskiLocallyFactorsThrough {S : Scheme.{u}} {Y Z : AlgebraicSpace S}
    {X : GroupoidsOver S} (φ : Y ⟶ Z) (f : X ⟶ Z.toGroupoids) : Prop :=
  ∀ y : AlgebraicSpace.Points Y, ∃ W : AlgebraicSpace.OpenSubspace Y,
    y ∈ W.pointsSet ∧
      ∃ x : W.X.toGroupoids ⟶ X,
        Nonempty (x ≫ f ≅ AlgebraicSpace.toGroupoids.map (W.ι ≫ φ))

/-- Unfolding of `zariskiLocallyFactorsThrough`. -/
theorem zariskiLocallyFactorsThrough_iff {S : Scheme.{u}}
    {Y Z : AlgebraicSpace S} {X : GroupoidsOver S} (φ : Y ⟶ Z)
    (f : X ⟶ Z.toGroupoids) :
    zariskiLocallyFactorsThrough φ f ↔
      ∀ y : AlgebraicSpace.Points Y, ∃ W : AlgebraicSpace.OpenSubspace Y,
        y ∈ W.pointsSet ∧
          ∃ x : W.X.toGroupoids ⟶ X,
            Nonempty (x ≫ f ≅ AlgebraicSpace.toGroupoids.map (W.ι ≫ φ)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
