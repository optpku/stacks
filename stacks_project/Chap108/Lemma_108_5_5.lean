/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_5_4
public import stacks_project.Chap108.Lemma_108_5_6_Map

/-!
# Lemma 108.5.5

An affine open immersion of separated finite-presentation algebraic spaces
over `B` induces an open immersion of Grothendieck Quot functors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- Lemma 108.5.5: If `π : X ⟶ Y` is an affine open immersion of algebraic
spaces which are separated and of finite presentation over an algebraic space
`B`, and `F` is a quasi-coherent `𝒪_X`-module, then the morphism
`map π y F : quot (π ≫ y) F ⟶ quot y ((Modules.pushforward π).obj F)` of
Lemma 108.5.4 is an open immersion of functors of algebraic spaces over `B`. -/
@[stacks 0DP2]
theorem isOpenImmersion_map (π : X ⟶ Y) (y : Y ⟶ B) (F : X.Modules)
    [Affine π] [IsOpenImmersion π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent] :
    IsOpenImmersionOnSchemesOver (map π y F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
