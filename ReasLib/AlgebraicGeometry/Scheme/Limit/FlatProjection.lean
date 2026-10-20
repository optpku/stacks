/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatCompatibility

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ Scheme.{u})
variable (t : D ⟶ (Functor.const (OrderDual I)).obj S)
variable (c : Cone D) (hc : IsLimit c)
variable [hD_affine : ∀ i : I, IsAffineHom (t.app (OrderDual.toDual i))]
variable [htransition_flat : ∀ (i j : I) (h : i ≤ j), Flat (D.map (homOfLE h))]

include hc hD_affine htransition_flat

/-- Every projection of a directed limit of schemes affine over a common base with flat
transition maps is flat. -/
theorem flatProjection (i : I) : Flat (c.π.app (OrderDual.toDual i)) := sorry

variable [hS_catenary : UniversallyCatenary S]
variable [hD_catenary : ∀ i : OrderDual I, UniversallyCatenary (D.obj i)]
variable [hc_catenary : UniversallyCatenary c.pt]
variable (g : c.pt ⟶ S) [hg_flat : Flat g]
variable (hπ : c.π ≫ t = (Functor.const (OrderDual I)).map g)
variable (δ : S → ℤ) [hδ : IsDimensionFunction δ]
variable (δ' : c.pt → ℤ) [hδ' : IsDimensionFunction δ']
variable [hD_dimension : ∀ i : I,
  IsDimensionFunction (fun point ↦ δ (t.app (OrderDual.toDual i) point))]
variable [hstage_flat : ∀ i : I, Flat (t.app (OrderDual.toDual i))]
variable (hcompat : g.IsDimensionFunctionCompatible δ δ' 0)
variable (hstage : ∀ i : I,
  @Scheme.Hom.IsDimensionFunctionCompatible S (D.obj (OrderDual.toDual i))
    hS_catenary (hD_catenary _) (t.app (OrderDual.toDual i)) (hstage_flat i)
    δ hδ (fun point ↦ δ (t.app (OrderDual.toDual i) point)) (hD_dimension i) 0)
variable (htransition : ∀ (i j : I) (h : i ≤ j),
  @Scheme.Hom.IsDimensionFunctionCompatible
    (D.obj (OrderDual.toDual i)) (D.obj (OrderDual.toDual j))
    (hD_catenary _) (hD_catenary _) (D.map (homOfLE h)) (htransition_flat i j h)
    (fun point ↦ δ (t.app (OrderDual.toDual i) point)) (hD_dimension i)
    (fun point ↦ δ (t.app (OrderDual.toDual j) point)) (hD_dimension j) 0)

include hcompat hstage htransition hπ in
/-- At a generic point of a projection fiber of a directed affine limit, the limit
dimension function equals the composite stage dimension function with zero shift. -/
theorem projectionDimension_eq (i : I) (point : D.obj (OrderDual.toDual i))
    (genericPoint : (c.π.app (OrderDual.toDual i)).fiber point)
    (hgeneric : genericPoint ∈ genericPoints ((c.π.app (OrderDual.toDual i)).fiber point)) :
    δ' ((c.π.app (OrderDual.toDual i)).fiberι point genericPoint) =
      δ (t.app (OrderDual.toDual i) point) + 0 := sorry

end AlgebraicGeometry.Scheme.Limit
