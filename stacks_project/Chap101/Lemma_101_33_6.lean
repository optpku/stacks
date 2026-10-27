/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth.SourceLocus
import StacksCheckRecall

/-!
# Largest open substack on which a morphism of algebraic stacks is smooth
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/- Lemma 101.33.6 (1): Every morphism of algebraic stacks has a largest open
source substack on which its restriction is smooth. -/
@[stacks 0DZR] #check (AlgebraicGeometry.AlgebraicStack.Smooth.sourceLocus_isLargest :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Smooth ((sourceLocus f).inclusion ≫ f) ∧
      ∀ V : Substack.Open X,
        Smooth (V.inclusion ≫ f) → V.pointsSet ⊆ (sourceLocus f).pointsSet)

/- Lemma 101.33.6 (2): The smooth source locus commutes with smooth precomposition. -/
@[stacks 0DZR] #check (AlgebraicGeometry.AlgebraicStack.Smooth.sourceLocus_comp_eq_preimage :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ X) [Smooth g],
    (sourceLocus (g ≫ f)).pointsSet = Points.map g ⁻¹' (sourceLocus f).pointsSet)

/- Lemma 101.33.6 (3): The smooth source locus commutes with flat, locally
finitely presented base change. -/
@[stacks 0DZR] #check (AlgebraicGeometry.AlgebraicStack.Smooth.sourceLocus_eq_preimage_of_flat_locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat g] [LocallyOfFinitePresentation g],
    (sourceLocus (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)).pointsSet =
      Points.map (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) ⁻¹'
        (sourceLocus f).pointsSet)

/- Lemma 101.33.6 (4): For a locally finitely presented morphism, the smooth
source locus commutes with flat base change. -/
@[stacks 0DZR] #check (AlgebraicGeometry.AlgebraicStack.Smooth.sourceLocus_eq_preimage_of_flat_base :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFinitePresentation f] [Flat g],
    (sourceLocus (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)).pointsSet =
      Points.map (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) ⁻¹'
        (sourceLocus f).pointsSet)

end AlgebraicGeometry.AlgebraicStack.Smooth
