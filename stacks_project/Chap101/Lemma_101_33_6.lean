/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap100.Lemma_100_9_18_SourceLocus
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_33_6_SourceLocus
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Largest open substack on which a morphism of algebraic stacks is smooth

There is a largest open substack of the source on which a morphism of algebraic
stacks is smooth. Formation of this open commutes with precomposition by smooth
morphisms, with 2-fibre-product base change along flat locally-of-finite-presentation
morphisms, and with base change along flat morphisms when the original morphism
is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- Lemma 101.33.6 (1): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
There is a largest open substack `U ⊂ X` such that `U.ι ≫ f` is smooth. -/
@[stacks 0DZR]
theorem sourceLocus_isLargest {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Smooth ((sourceLocus f).ι ≫ f) ∧
      ∀ V : OpenSubstack X,
        Smooth (V.ι ≫ f) → V.pointsSet ⊆ (sourceLocus f).pointsSet :=
  sorry

/-- Lemma 101.33.6 (2): Formation of the largest open substack of the source on
which `f` is smooth commutes with precomposition by a smooth morphism. -/
@[stacks 0DZR]
theorem sourceLocus_comp_eq_preimage {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ X) [Smooth g] :
    (sourceLocus (g ≫ f)).pointsSet =
      Points.map g ⁻¹' (sourceLocus f).pointsSet :=
  sorry

/-- Lemma 101.33.6 (3): Formation of the largest open substack of the source on
which `f` is smooth commutes with base change along a morphism which is flat
and locally of finite presentation. -/
@[stacks 0DZR]
theorem sourceLocus_eq_pullback_of_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    (sourceLocus (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)).pointsSet =
      ((sourceLocus f).pullback f g).pointsSet :=
  sorry

/-- Lemma 101.33.6 (4): Formation of the largest open substack of the source on
which `f` is smooth commutes with base change along a flat morphism, provided
`f` is locally of finite presentation. -/
@[stacks 0DZR]
theorem sourceLocus_eq_pullback_of_flat_base
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFinitePresentation f] [Flat g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    (sourceLocus (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)).pointsSet =
      ((sourceLocus f).pullback f g).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
