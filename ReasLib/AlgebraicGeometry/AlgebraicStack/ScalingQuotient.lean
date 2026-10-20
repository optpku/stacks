/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Topology.Defs.Filter
public import ReasLib.AlgebraicGeometry.AffineSpace.Scaling
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The quotient stack `[𝔸¹ / 𝔾ₘ]` for the usual scaling action over a field. -/
@[reducible]
def affineLineQuotient (k : Type u) [Field k] : GroupoidsOver (Spec (.of k)) :=
  quotient (𝔾ₘ[Spec (.of k)]).toGrp (AffineSpace.scalingAction k)

/-- `affineLineQuotient` is the quotient stack of the usual scaling action. -/
theorem affineLineQuotient_spec (k : Type u) [Field k] :
    affineLineQuotient k = quotient (𝔾ₘ[Spec (.of k)]).toGrp (AffineSpace.scalingAction k) :=
  rfl

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.AffineLineQuotient

open AffineSpace GroupoidAlgebraicSpace GroupoidScheme

/-- The atlas `𝔸¹ ⟶ [𝔸¹ / 𝔾ₘ]` of the scaling quotient stack. -/
def atlas (k : Type u) [Field k] :
    GroupoidsOver.slice (affineLineOver k) ⟶ affineLineQuotient k :=
  (AlgebraicSpace.ofOverSliceEquiv (scalingAction k).X).inv ≫
    SmallQuotient.atlas (ofScheme (ofAction (𝔾ₘ[Spec (.of k)]).toGrp (scalingAction k)))

/-- The origin of the affine line over `k`, as a scheme point. -/
def origin (k : Type u) [Field k] : affineLine k :=
  homOfVector (𝟙 (Spec (.of k))) (fun _ ↦ 0) (default : Spec (.of k))

/-- The unit section of the affine line over `k`, as a scheme point. -/
def unitSection (k : Type u) [Field k] : affineLine k :=
  homOfVector (𝟙 (Spec (.of k))) (fun _ ↦ 1) (default : Spec (.of k))

/-- The closed point of `[𝔸¹ / 𝔾ₘ]`, the atlas image of the origin of `𝔸¹`. -/
def closedPoint (k : Type u) [Field k] : Points (affineLineQuotient k) :=
  Points.mapSlice (atlas k) (origin k)

/-- The generic point of `[𝔸¹ / 𝔾ₘ]`, the atlas image of the unit section of `𝔸¹`. -/
def genericPoint (k : Type u) [Field k] : Points (affineLineQuotient k) :=
  Points.mapSlice (atlas k) (unitSection k)

/-- `closedPoint` is the image of the origin along the quotient atlas. -/
theorem closedPoint_spec (k : Type u) [Field k] :
    closedPoint k = Points.mapSlice (atlas k) (origin k) :=
  rfl

/-- `genericPoint` is the image of the unit section along the quotient atlas. -/
theorem genericPoint_spec (k : Type u) [Field k] :
    genericPoint k = Points.mapSlice (atlas k) (unitSection k) :=
  rfl

/-- The two `𝔾ₘ`-orbits on `𝔸¹`, as points of `[𝔸¹ / 𝔾ₘ]`. -/
def pointsEmbedding (k : Type u) [Field k] :
    Fin 2 ↪ Points (affineLineQuotient k) where
  toFun i := if i = 0 then genericPoint k else closedPoint k
  inj' := sorry

/-- The points space of `[𝔸¹ / 𝔾ₘ]` is finite, with elements the two orbit points. -/
instance instFintype_points (k : Type u) [Field k] :
    Fintype (Points (affineLineQuotient k)) where
  elems := Finset.map (pointsEmbedding k) Finset.univ
  complete := sorry

/-- The points space of `[𝔸¹ / 𝔾ₘ]` has two points,
corresponding to the two orbits of `𝔾ₘ` on `𝔸¹`. -/
theorem card_points (k : Type u) [Field k] :
    Fintype.card (Points (affineLineQuotient k)) = 2 :=
  sorry

/-- The generic orbit point of `[𝔸¹ / 𝔾ₘ]` specializes to the
closed orbit point. -/
theorem specializes (k : Type u) [Field k] :
    Specializes (genericPoint k) (closedPoint k) :=
  sorry

/-- The underlying topological space of `[𝔸¹ / 𝔾ₘ]` has
Krull dimension `1`. -/
theorem topologicalKrullDim_eq_one (k : Type u) [Field k] :
    topologicalKrullDim (Points (affineLineQuotient k)) = (1 : WithBot ℕ∞) :=
  sorry

/-- The stacky dimension of `[𝔸¹ / 𝔾ₘ]` is `0` at every point. -/
theorem dimensionAt_eq_zero (k : Type u) [Field k]
    (x : Points (affineLineQuotient k)) : dimensionAt x = (0 : EInt) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.AffineLineQuotient

