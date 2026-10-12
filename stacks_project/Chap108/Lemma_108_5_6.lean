/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap108.Lemma_108_5_6_Map

/-!
# Lemma 108.5.6

An open immersion of separated finite-presentation algebraic spaces over `B`
induces an open immersion of Grothendieck Quot functors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- Lemma 108.5.6: If `j : X ⟶ Y` is an open immersion of algebraic spaces which
are separated and of finite presentation over an algebraic space `B`, and `G`
is a quasi-coherent `𝒪_Y`-module, then `j` induces an open immersion
`openMap j y G : quot (j ≫ y) ((Modules.pullback j).obj G) ⟶ quot y G` of functors
of algebraic spaces over `B`. -/
@[stacks 0DP3]
theorem isOpenImmersion_map {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (j : X ⟶ Y) (y : Y ⟶ B) [IsOpenImmersion j]
    [Separated (j ≫ y)] [FinitePresentation (j ≫ y)]
    [Separated y] [FinitePresentation y]
    (G : Y.Modules) [G.IsQuasicoherent] :
    IsOpenImmersionOnSchemesOver (openMap j y G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
