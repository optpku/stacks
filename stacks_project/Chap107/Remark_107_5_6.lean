/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ScalingQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Classifying.MultiplicativeGroup
import StacksCheckRecall

/-!
# Dimension of Deligne–Mumford stacks versus the space of points

For quasi-separated locally Noetherian Deligne–Mumford stacks, local dimension
agrees with local topological dimension. The scaling quotient and the classifying
stack of the multiplicative group illustrate the difference for Artin stacks.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicStack
open scoped AlgebraicGeometry Bicategory

universe u

/- Remark 107.5.6: for a quasi-separated locally Noetherian Deligne–Mumford stack,
local dimension agrees with the local topological Krull dimension. -/
@[stacks 0DRK] #check
  (AlgebraicGeometry.DeligneMumfordStack.dimensionAt_eq_topologicalKrullDimAt :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [DeligneMumfordStack X]
      [AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian X]
      [AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated X] (x : Points X),
      dimensionAt x = dimensionToEInt (topologicalKrullDimAt x))

/- The scaling quotient has exactly two orbit points. -/
#check (AlgebraicGeometry.AlgebraicStack.AffineLineQuotient.card_points :
  ∀ (k : Type u) [Field k], Fintype.card (Points (affineLineQuotient k)) = 2)

/- The nonzero orbit specializes to the zero orbit. -/
#check (AlgebraicGeometry.AlgebraicStack.AffineLineQuotient.specializes :
  ∀ (k : Type u) [Field k],
    Specializes (AffineLineQuotient.genericPoint k) (AffineLineQuotient.closedPoint k))

/- The space of points of the scaling quotient has dimension one. -/
#check (AlgebraicGeometry.AlgebraicStack.AffineLineQuotient.topologicalKrullDim_eq_one :
  ∀ (k : Type u) [Field k],
    topologicalKrullDim (Points (affineLineQuotient k)) = (1 : WithBot ℕ∞))

/- The scaling quotient has stack dimension zero at every point. -/
#check (AlgebraicGeometry.AlgebraicStack.AffineLineQuotient.dimensionAt_eq_zero :
  ∀ (k : Type u) [Field k] (x : Points (affineLineQuotient k)), dimensionAt x = (0 : EInt))

/- The multiplicative-group classifying stack has a unique point. -/
#check (AlgebraicGeometry.AlgebraicStack.instUnique_points_classifying_multiplicativeGroup :
  ∀ (k : Type u) [Field k], Unique (Points (classifying (𝔾ₘ[Spec (.of k)]).toGrp)))

/- The multiplicative-group classifying stack has dimension minus one at every point. -/
#check (AlgebraicGeometry.AlgebraicStack.dimensionAt_classifying_multiplicativeGroup :
  ∀ (k : Type u) [Field k] (x : Points (classifying (𝔾ₘ[Spec (.of k)]).toGrp)),
    dimensionAt x = ((-1 : ℤ) : EInt))
