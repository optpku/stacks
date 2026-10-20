module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Full

/-!
# Fibre products in the category of formal algebraic spaces

Formal algebraic spaces on the full big fppf site over a scheme are closed
under walking-cospan limits. Their full subcategory therefore has fibre
products, created by the inclusion into the ambient sheaf category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ObjectProperty AlgebraicGeometry
open ChosenBigFppfSite

noncomputable section

universe u

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Formal algebraic spaces on the full big fppf site over a scheme are closed
under walking-cospan limits of sheaves. -/
instance instIsClosedUnderPullbacks {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))] :
    IsClosedUnderLimitsOfShape
      (fun X : Sheaf (full.bigTopology S) (Type (u + 1)) => IsFormalAlgebraicSpace X)
      WalkingCospan :=
  sorry

/-- The sheaf fibre product of morphisms of formal algebraic spaces on the
full big fppf site over a scheme is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_pullback {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    {X Y Z : Sheaf (full.bigTopology S) (Type (u + 1))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsFormalAlgebraicSpace (pullback f g) := by
  apply ObjectProperty.prop_limit
    (fun X : Sheaf (full.bigTopology S) (Type (u + 1)) => IsFormalAlgebraicSpace X)
    (cospan f g)
  intro j
  cases j with
  | none => assumption
  | some j => cases j <;> assumption

/-- The category of formal algebraic spaces on the full big fppf site over a
scheme has fibre products. -/
instance instHasPullbacks {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))] :
    HasPullbacks
      (ObjectProperty.FullSubcategory fun X : Sheaf (full.bigTopology S) (Type (u + 1)) =>
        IsFormalAlgebraicSpace X) :=
  inferInstance

end AlgebraicGeometry.IsFormalAlgebraicSpace
