module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.PairFiberMap
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.18.3: In the cartesian square (68.18.0.1) of algebraic spaces over a
scheme `S`, if `hZ : Z' ⟶ Z` is a morphism and `z' ∈ |Z'|` maps to `z`, then the
induced map `F_{x, z'} → F_{x, z}` is surjective. Here `W' = X ×_Y Z' = W ×_Z Z'`,
and the map is the restriction of `|W'| → |W|`. -/
@[stacks 0AC5] #check (AlgebraicGeometry.AlgebraicSpace.Points.fibreMap_surjective :
  ∀ {S : Scheme.{u}} {W W' X Z Z' : AlgebraicSpace S}
    {p : W ⟶ X} {q : W ⟶ Z} {p' : W' ⟶ X} {q' : W' ⟶ Z'}
    (φ : W' ⟶ W) (hZ : Z' ⟶ Z) (hφ : IsPullback φ q' q hZ) (hp : φ ≫ p = p')
    (x : Points X) (z' : Points Z') (z : Points Z) (hz : Points.map hZ z' = z),
    Function.Surjective (Points.fibreMap φ hZ hp hφ.w x z' z hz))
