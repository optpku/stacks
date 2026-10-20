module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.PairFiber

/-!
# Induced maps on point-fibres of algebraic spaces

A morphism `Z' ⟶ Z` over a cartesian square induces a map of point-fibres
`F_{x, z'} → F_{x, z}` by restriction of the map on points of the apex.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

variable {S : Scheme.{u}}

section

variable {W W' X Z Z' : AlgebraicSpace S}
variable {p : W ⟶ X} {q : W ⟶ Z} {p' : W' ⟶ X} {q' : W' ⟶ Z'}
variable (φ : W' ⟶ W) (hZ : Z' ⟶ Z)

/-- The map on points induced by `φ` sends the fibre over `x` and `z'` into the
fibre over `x` and `z`. -/
theorem fibre_mapsTo (hp : φ ≫ p = p') (hq : φ ≫ q = q' ≫ hZ) (x : Points X)
    (z' : Points Z') (z : Points Z) (hz : map hZ z' = z) :
    Set.MapsTo (map φ) (fibre p' q' x z') (fibre p q x z) :=
  sorry

/-- The induced map of point-fibres along a morphism `Z' ⟶ Z`. -/
def fibreMap (hp : φ ≫ p = p') (hq : φ ≫ q = q' ≫ hZ) (x : Points X)
    (z' : Points Z') (z : Points Z) (hz : map hZ z' = z) :
    fibre p' q' x z' → fibre p q x z :=
  Set.MapsTo.restrict (map φ) (fibre p' q' x z') (fibre p q x z)
    (fibre_mapsTo φ hZ hp hq x z' z hz)

/-- Applying the induced fibre map is the map on points induced by `φ`. -/
theorem fibreMap_apply (hp : φ ≫ p = p') (hq : φ ≫ q = q' ≫ hZ) (x : Points X)
    (z' : Points Z') (z : Points Z) (hz : map hZ z' = z)
    (w : fibre p' q' x z') :
    (fibreMap φ hZ hp hq x z' z hz w : Points W) = map φ (w : Points W') :=
  sorry

/-- On a cartesian square `W' ⟶ W` over `Z' ⟶ Z`, the induced map of point-fibres
is surjective. -/
theorem fibreMap_surjective (hφ : IsPullback φ q' q hZ) (hp : φ ≫ p = p')
    (x : Points X) (z' : Points Z') (z : Points Z) (hz : map hZ z' = z) :
    Function.Surjective (fibreMap φ hZ hp hφ.w x z' z hz) :=
  sorry

/-- On a cartesian square `W' ⟶ W` over `Z' ⟶ Z`, `map φ` is surjective from the
fibre over `x` and `z'` onto the fibre over `x` and `z`. -/
theorem surjOn_map_fibre (hφ : IsPullback φ q' q hZ) (hp : φ ≫ p = p')
    (x : Points X) (z' : Points Z') (z : Points Z) (hz : map hZ z' = z) :
    Set.SurjOn (map φ) (fibre p' q' x z') (fibre p q x z) :=
  sorry

/-- On a cartesian square `W' ⟶ W` over `Z' ⟶ Z`, every point of the fibre over
`x` and `z` lifts along `φ` to a point of the fibre over `x` and `z'`. -/
theorem exists_mem_fibre (hφ : IsPullback φ q' q hZ) (hp : φ ≫ p = p')
    (x : Points X) (z' : Points Z') (z : Points Z) (hz : map hZ z' = z)
    (w : Points W) (hw : w ∈ fibre p q x z) :
    ∃ w' ∈ fibre p' q' x z', map φ w' = w :=
  sorry

end

section

variable {W X Z Z' : AlgebraicSpace S}
variable (p : W ⟶ X) (q : W ⟶ Z) (hZ : Z' ⟶ Z)

/-- The induced fibre map for a chosen fibre product `W ×_Z Z'`. -/
def fibreMap_pullback [HasPullback q hZ] (x : Points X) (z' : Points Z')
    (z : Points Z) (hz : map hZ z' = z) :
    fibre (pullback.fst q hZ ≫ p) (pullback.snd q hZ) x z' → fibre p q x z :=
  fibreMap (pullback.fst q hZ) hZ rfl pullback.condition x z' z hz

/-- The induced fibre map for a chosen fibre product `W ×_Z Z'` is surjective. -/
theorem fibreMap_pullback_surjective [HasPullback q hZ] (x : Points X)
    (z' : Points Z') (z : Points Z) (hz : map hZ z' = z) :
    Function.Surjective (fibreMap_pullback p q hZ x z' z hz) :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace.Points
