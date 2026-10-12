/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import stacks_project.Chap65.Lemma_65_7_1_Product
public import stacks_project.Chap72.Lemma_72_14_3_Geometrically

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

/-- Lemma 72.12.3: Let `k` be a field and let `X`, `Y` be algebraic spaces over `k`.
If `X` is geometrically connected over `k`, then the projection
`productSnd X Y : product X Y ⟶ Y` induces a bijection on connected components of
`Points (product X Y)` and `Points Y`. -/
@[stacks 0A11]
theorem productSnd_connectedComponentsMap_bijective {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} [GeometricallyConnected X] :
    Function.Bijective
      ((Points.continuous_map (productSnd X Y)).connectedComponentsMap :
        ConnectedComponents (Points (product X Y)) → ConnectedComponents (Points Y)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
