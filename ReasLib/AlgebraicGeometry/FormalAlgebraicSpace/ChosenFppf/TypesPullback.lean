/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalTypes
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.FiniteType

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- The pullback of two locally countably indexed formal algebraic spaces over
a common formal algebraic space is locally countably indexed. -/
instance instIsLocallyCountablyIndexed_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] [IsLocallyCountablyIndexed X]
    [IsLocallyCountablyIndexed Z] (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsLocallyCountablyIndexed (pullback f g) :=
  sorry

/-- The pullback of two locally classical formal algebraic spaces over a common
formal algebraic space is locally classical. -/
instance instIsLocallyClassical_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] [IsLocallyClassical X] [IsLocallyClassical Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsLocallyClassical (pullback f g) :=
  sorry

/-- The pullback of two locally weakly adic formal algebraic spaces over a
common formal algebraic space is locally weakly adic. -/
instance instIsLocallyWeaklyAdic_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] [IsLocallyWeaklyAdic X] [IsLocallyWeaklyAdic Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsLocallyWeaklyAdic (pullback f g) :=
  sorry

/-- The pullback of two locally adic* formal algebraic spaces over a common
formal algebraic space is locally adic*. -/
instance instIsLocallyAdicStar_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] [IsLocallyAdicStar X] [IsLocallyAdicStar Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsLocallyAdicStar (pullback f g) :=
  sorry

/-- The pullback of locally Noetherian formal algebraic spaces is locally
Noetherian when the induced map between their reductions is locally of finite
type on étale algebraic-space charts. -/
theorem instIsLocallyNoetherian_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace.IsLocallyNoetherian X]
    [IsFormalAlgebraicSpace.IsLocallyNoetherian Z] (f : X ⟶ Y) (g : Z ⟶ Y)
   
    (φ : IsFormalAlgebraicSpace.reduction X ⟶ IsFormalAlgebraicSpace.reduction Y)
    (hφ : φ ≫ IsFormalAlgebraicSpace.reductionι Y =
      IsFormalAlgebraicSpace.reductionι X ≫ f)
    (hft : locallyOfFiniteTypeOnEtaleSquares φ) :
    IsFormalAlgebraicSpace.IsLocallyNoetherian (pullback f g) :=
  sorry


end AlgebraicGeometry
end
