module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Connected
import StacksCheckRecall

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

/- Lemma 72.12.3: Let `k` be a field and let `X`, `Y` be algebraic spaces over `k`.
If `X` is geometrically connected over `k`, then the projection
`productSnd X Y : product X Y ⟶ Y` induces a bijection on connected components of
`Points (product X Y)` and `Points Y`. -/
@[stacks 0A11]
#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected.productSnd_connectedComponentsMap_bijective :
    ∀ {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} [GeometricallyConnected X],
    Function.Bijective
      ((Points.continuous_map (productSnd X Y)).connectedComponentsMap :
        ConnectedComponents (Points (product X Y)) → ConnectedComponents (Points Y)))
