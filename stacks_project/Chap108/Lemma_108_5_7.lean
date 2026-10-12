/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_20_6
public import stacks_project.Chap67.Lemma_67_45_8
public import stacks_project.Chap67.Lemma_67_45_10
public import stacks_project.Chap108.Lemma_108_5_4

/-!
# Lemma 108.5.7

A closed immersion of separated finite-presentation algebraic spaces over `B`
induces an isomorphism of Grothendieck Quot functors by fibrewise pushforward.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- Lemma 108.5.7: if `π : X ⟶ Y` is a closed immersion of algebraic spaces
which are separated and of finite presentation over an algebraic space `B`,
and `F` is a quasi-coherent `𝒪_X`-module, then the morphism
`map π y F : quot (π ≫ y) F ⟶ quot y ((Modules.pushforward π).obj F)` of
Lemma 108.5.4 is an isomorphism. -/
@[stacks 0DP4, instance]
theorem isIso_map (π : X ⟶ Y) (y : Y ⟶ B) [IsClosedImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso (map π y F) :=
  sorry

/-- The morphism of Lemma 108.5.4 is bijective on `T`-points for every scheme
`T` over `B`. -/
theorem map_app_bijective (π : X ⟶ Y) (y : Y ⟶ B) [IsClosedImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y]
    (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemesOver B)ᵒᵖ) :
    Function.Bijective ((map π y F).app σ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
