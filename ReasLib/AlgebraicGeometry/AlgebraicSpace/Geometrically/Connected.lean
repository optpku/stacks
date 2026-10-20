/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically

/-!
# Connected components of products with a geometrically connected factor

If `X` is geometrically connected over a field `k`, the projection `product X Y ⟶ Y`
induces a bijection on connected components of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected

/-- If `X` is a geometrically connected algebraic space over a field `k`, then for any
algebraic space `Y` over `k`, the projection `productSnd X Y : product X Y ⟶ Y`
induces a bijection on connected components of their spaces of points. -/
theorem productSnd_connectedComponentsMap_bijective {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} [GeometricallyConnected X] :
    Function.Bijective
      ((Points.continuous_map (productSnd X Y)).connectedComponentsMap :
        ConnectedComponents (Points (product X Y)) → ConnectedComponents (Points Y)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
