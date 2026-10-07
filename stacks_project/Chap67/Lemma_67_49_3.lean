module

public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Codimension-zero points under flat morphisms of algebraic spaces

A flat morphism of algebraic spaces sends points of codimension `0` to points of
codimension `0`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Flat

/-- Lemma 67.49.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
algebraic spaces over `S`. Then for `x ∈ |X|` we have: `x` has codimension `0`
in `X` implies `f(x)` has codimension `0` in `Y`.

A point of codimension `0` means `localRingDimAt _ = 0`, and `f(x)` is
`Points.map f x`. -/
@[stacks 0GMC]
theorem localRingDimAt_map_eq_zero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] {x : Points X} (hx : localRingDimAt x = 0) :
    localRingDimAt (Points.map f x) = 0 :=
  sorry

/-- The map on points induced by a flat morphism of algebraic spaces sends
codimension-`0` points of `X` into the codimension-`0` points of `Y`. -/
theorem mapsTo_localRingDimAt_eq_zero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] :
    Set.MapsTo (Points.map f) (setOf fun x : Points X ↦ localRingDimAt x = 0)
      (setOf fun y : Points Y ↦ localRingDimAt y = 0) :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicSpace
