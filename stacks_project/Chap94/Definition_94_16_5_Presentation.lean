module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_4_Smooth
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation

/-!
# Presentations of algebraic stacks

A presentation of an algebraic stack `X` over `S` is a smooth groupoid in algebraic
spaces over `S` together with an equivalence from its quotient stack to `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Presentation :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Type (u + 1))

namespace Presentation

#check (AlgebraicGeometry.AlgebraicStack.Presentation.of :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (G : GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))))
    [GroupoidAlgebraicSpace.Smooth G] (f : G.quotientStack ⟶ X)
    (hf : (FiberedCategoryOver.Groupoids.toBasedFunctor f).IsEquivalence),
    Presentation X)

#check (AlgebraicGeometry.AlgebraicStack.Presentation.of_groupoid :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (G : GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))))
    [GroupoidAlgebraicSpace.Smooth G] (f : G.quotientStack ⟶ X)
    (hf : (FiberedCategoryOver.Groupoids.toBasedFunctor f).IsEquivalence),
    (of G f hf).groupoid = G)

#check (AlgebraicGeometry.AlgebraicStack.Presentation.of_hom :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (G : GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))))
    [GroupoidAlgebraicSpace.Smooth G] (f : G.quotientStack ⟶ X)
    (hf : (FiberedCategoryOver.Groupoids.toBasedFunctor f).IsEquivalence),
    (of G f hf).hom = f)

#check (AlgebraicGeometry.AlgebraicStack.Presentation.spec :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : Presentation X),
    GroupoidAlgebraicSpace.Smooth P.groupoid ∧
      (FiberedCategoryOver.Groupoids.toBasedFunctor P.hom).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicStack.Presentation.smooth :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : Presentation X),
    GroupoidAlgebraicSpace.Smooth P.groupoid)

#check (AlgebraicGeometry.AlgebraicStack.Presentation.hom_isEquivalence :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : Presentation X),
    (FiberedCategoryOver.Groupoids.toBasedFunctor P.hom).IsEquivalence)

end Presentation

end AlgebraicGeometry.AlgebraicStack
