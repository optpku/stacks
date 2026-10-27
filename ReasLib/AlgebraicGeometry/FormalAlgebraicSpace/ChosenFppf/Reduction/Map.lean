/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
  [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
  [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]

/-- The morphism on reductions induced by a morphism of formal algebraic spaces. -/
def mapReduction (h_size : ChosenBigSite.IsSizeClosed 𝒮)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    reduction X ⟶ reduction Y :=
  Classical.choose (@existsUnique_mapReduction 𝒮 S _ _ ⟨h_size⟩ X Y _ _ f)

/-- The induced morphism on reductions is the unique morphism compatible
with the reduction inclusions. -/
theorem mapReduction_spec (h_size : ChosenBigSite.IsSizeClosed 𝒮)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    mapReduction h_size f ≫ reductionι Y = reductionι X ≫ f ∧
      ∀ φ : reduction X ⟶ reduction Y,
        φ ≫ reductionι Y = reductionι X ≫ f → φ = mapReduction h_size f := sorry

/-- The reduction of a formal algebraic space is a formal algebraic space. -/
theorem isFormalAlgebraicSpace_reduction (h_size : ChosenBigSite.IsSizeClosed 𝒮)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsFormalAlgebraicSpace X] :
    IsFormalAlgebraicSpace (reduction X) := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
