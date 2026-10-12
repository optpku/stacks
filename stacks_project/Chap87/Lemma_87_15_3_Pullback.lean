/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap87.Definition_87_11_1_Formal

/-!
# Fibre products in the category of formal algebraic spaces

The full subcategory of fppf sheaves on `(Sch/S)_fppf` cut out by
`IsFormalAlgebraicSpace` is closed under walking-cospan limits, so it
has fibre products, created by the inclusion from the ambient sheaf
category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ObjectProperty AlgebraicGeometry
open ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Formal algebraic spaces over `S` are closed under fibre products of
sheaves. -/
instance instIsClosedUnderPullbacks {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))] :
    IsClosedUnderLimitsOfShape
      (fun X : Sheaf (𝒮.bigTopology S) (Type (max u v)) => IsFormalAlgebraicSpace X)
      WalkingCospan :=
  sorry

/-- The sheaf fibre product of morphisms of formal algebraic spaces over `S`
is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsFormalAlgebraicSpace (pullback f g) :=
  sorry

/-- The category of formal algebraic spaces over `S` has fibre products. -/
instance instHasPullbacks {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))] :
    HasPullbacks
      (ObjectProperty.FullSubcategory fun X : Sheaf (𝒮.bigTopology S) (Type (max u v)) =>
        IsFormalAlgebraicSpace X) :=
  inferInstance

end AlgebraicGeometry.IsFormalAlgebraicSpace
