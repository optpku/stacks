module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.Cospan.ProperPushforward

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Remark 42.33.8 (1): degree-`p` bivariant Chow operations on a cospan
`X ⟶ Z ⟵ Y`, compatible with proper pushforward, flat pullback of fixed
relative dimension, and effective-Cartier Gysin pullback. -/
@[stacks 0FDU] #check (AlgebraicGeometry.BivariantClass.Cospan :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom]
    (l : X ⟶ Z) (r : Y ⟶ Z) (p : ℤ), Type (u + 1))

/- Remark 42.33.8 (2): a proper morphism `f : X₂ ⟶ X₁` defines a degree-zero
bivariant cospan operation on `X₁ ⟶ X₁ ⟵ X₂` by proper pushforward after every
base change. -/
@[stacks 0FDU] #check (AlgebraicGeometry.BivariantClass.Cospan.properPushforward :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S}
    [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left],
      AlgebraicGeometry.BivariantClass.Cospan delta (𝟙 X₁) f 0)
