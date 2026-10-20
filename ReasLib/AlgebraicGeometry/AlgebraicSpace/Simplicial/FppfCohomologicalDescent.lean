/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHypercovering

/-! # Étale cohomological descent for fppf hypercoverings -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- For an fppf hypercovering, the derived unit of total étale augmentation is
invertible on every bounded-below complex of abelian étale sheaves. -/
theorem plusDerivedUnit_app_isIso (ha : IsFppfHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((plusDerivedUnit a).app K) :=
  sorry

/-- The derived unit of total étale augmentation for an fppf hypercovering is
an isomorphism of functors on the bounded-below derived category. -/
theorem plusDerivedUnit_isIso (ha : IsFppfHypercovering a) : IsIso (plusDerivedUnit a) :=
  (NatTrans.isIso_iff_isIso_app (plusDerivedUnit a)).2 (plusDerivedUnit_app_isIso a ha)

end AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived
