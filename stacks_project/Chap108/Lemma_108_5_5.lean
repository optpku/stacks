module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.OpenImmersion

/-!
# Lemma 108.5.5

An affine open immersion of separated finite-presentation algebraic spaces
over `B` induces an open immersion of Grothendieck Quot functors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.5.5: If `π : X ⟶ Y` is an affine open immersion of algebraic
spaces which are separated and of finite presentation over an algebraic space
`B`, and `F` is a quasi-coherent `𝒪_X`-module, then the morphism
`map π y F : quot (π ≫ y) F ⟶ quot y ((Modules.pushforward π).obj F)` of
Lemma 108.5.4 is an open immersion of functors of algebraic spaces over `B`. -/
@[stacks 0DP2] #check (AlgebraicGeometry.AlgebraicSpace.Quot.isOpenImmersion_map :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (π : X ⟶ Y) (y : Y ⟶ B)
    (F : X.Modules) [Affine π] [IsOpenImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent],
    Quot.IsOpenImmersionOnSchemesOver (AlgebraicGeometry.AlgebraicSpace.Quot.map π y F))
