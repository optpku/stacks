/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Over.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Over.Composition

/-!
# Composition of flat pullbacks

This file records the degree transport and composition law for flat pullback on cycle groups.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Successive shifts by relative dimensions `s` and `r` agree with the shift by `r + s`. -/
theorem flatPullback_comp_degree (k : ℤ) (r s : ℕ) :
    (k + (s : ℤ)) + (r : ℤ) = k + ((r + s : ℕ) : ℤ) := sorry

/-- For composable flat morphisms of fixed relative dimensions, successive pullback of cycles
equals pullback along the composite after reindexing the resulting degree. -/
theorem flatPullback_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y Z : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z) (r s : ℕ) [Flat f.left] [Flat g.left]
    [Scheme.Hom.RelativeDimension f.left r] [Scheme.Hom.RelativeDimension g.left s]
    (k : ℤ) :
    (reindex (X.hom.relativeDimensionFunction δ) (flatPullback_comp_degree k r s)).comp
        ((flatPullback δ X Y f r (k + (s : ℤ))).comp
          (flatPullback δ Y Z g s k)) =
      flatPullback δ X Z (f ≫ g) (r + s) k := sorry

end AlgebraicGeometry.CycleGroup
