module

public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import stacks_project.Chap76.Lemma_76_52_4_Triangulated
public import stacks_project.Chap76.Lemma_76_52_4_Retracts
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.52.4 (1): for a scheme `S` and a flat, locally finitely presented morphism
`f : X ⟶ Y` of algebraic spaces over `S`, the `Y`-perfect objects of `D(𝒪_X)` form a
triangulated subcategory. -/
@[stacks 0DKR] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.perfectRelativeTo_isTriangulated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Flat f] [LocallyOfFinitePresentation f],
      ObjectProperty.IsTriangulated
        (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.perfectRelativeTo f))

/- Lemma 76.52.4 (2): for a scheme `S` and a flat, locally finitely presented morphism
`f : X ⟶ Y` of algebraic spaces over `S`, the `Y`-perfect objects of `D(𝒪_X)` form a
saturated subcategory. -/
@[stacks 0DKR] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.perfectRelativeTo_isStableUnderRetracts :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Flat f] [LocallyOfFinitePresentation f],
      ObjectProperty.IsStableUnderRetracts
        (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.perfectRelativeTo f))
