/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Union
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

/-!
# Smooth source loci of morphisms of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- The union of all open substacks of the source on which a morphism is smooth. -/
def sourceLocus {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Substack.Open X :=
  ⟨Substack.iUnion (fun U : {U : Substack.Open X // Smooth (U.inclusion ≫ f)} =>
      U.val.val),
    Substack.isOpen_iUnion _ (fun U => U.val.property)⟩

/-- The smooth source locus has smooth restriction and contains the point image
of every open substack on which the morphism restricts smoothly. -/
theorem sourceLocus_isLargest {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Smooth ((sourceLocus f).inclusion ≫ f) ∧
      ∀ V : Substack.Open X,
        Smooth (V.inclusion ≫ f) → V.pointsSet ⊆ (sourceLocus f).pointsSet := sorry

/-- The restriction of a morphism to its smooth source locus is smooth. -/
instance instSmoothSourceLocus {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Smooth ((sourceLocus f).inclusion ≫ f) := sorry

/-- The smooth source locus commutes with precomposition by a smooth morphism. -/
theorem sourceLocus_comp_eq_preimage {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ X) [Smooth g] :
    (sourceLocus (g ≫ f)).pointsSet =
      Points.map g ⁻¹' (sourceLocus f).pointsSet := sorry

/-- The smooth source locus commutes with flat, locally finitely presented base change. -/
theorem sourceLocus_eq_preimage_of_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat g] [LocallyOfFinitePresentation g] :
    (sourceLocus (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)).pointsSet =
      Points.map (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) ⁻¹'
        (sourceLocus f).pointsSet := sorry

/-- For a locally finitely presented morphism, the smooth source locus commutes
with flat base change. -/
theorem sourceLocus_eq_preimage_of_flat_base
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFinitePresentation f] [Flat g] :
    (sourceLocus (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)).pointsSet =
      Points.map (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) ⁻¹'
        (sourceLocus f).pointsSet := sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
