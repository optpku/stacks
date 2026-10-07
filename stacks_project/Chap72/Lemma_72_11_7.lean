module

public import stacks_project.Chap67.Definition_67_39_1_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap72.Definition_72_11_1_GeometricallyReduced

/-!
# Étale-local invariance of geometric reducedness

Geometric reducedness of algebraic spaces over a field is étale-local: it is
detected at a point after a morphism étale at that point, and globally after a
surjective étale morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.11.7 (1): Let `k` be a field. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `k`. Let `x` be a point of `|X|` with image `y` in `|Y|`.
If `f` is étale at `x`, then `X` is geometrically reduced at `x` if and only if
`Y` is geometrically reduced at `y`. -/
@[stacks 0E05]
theorem geometricallyReducedAt_iff_of_etaleAt {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} (f : X ⟶ Y) {x : Points X}
    (hf : EtaleAt f x) :
    GeometricallyReducedAt X x ↔ GeometricallyReducedAt Y (Points.map f x) :=
  sorry

/-- Lemma 72.11.7 (2): Let `k` be a field. Let `f : X ⟶ Y` be a surjective étale
morphism of algebraic spaces over `k`. Then `X` is geometrically reduced if and
only if `Y` is geometrically reduced. -/
@[stacks 0E05]
theorem geometricallyReduced_iff_of_surjective_etale {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} (f : X ⟶ Y) [Etale f] [Surjective f] :
    GeometricallyReduced X ↔ GeometricallyReduced Y :=
  sorry

/-- If `f` is étale at `x` and `X` is geometrically reduced at `x`, then `Y` is
geometrically reduced at the image of `x`. -/
theorem geometricallyReducedAt_map_of_etaleAt {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} (f : X ⟶ Y) {x : Points X}
    (hf : EtaleAt f x) (hx : GeometricallyReducedAt X x) :
    GeometricallyReducedAt Y (Points.map f x) :=
  sorry

/-- If `f` is étale at `x` and `Y` is geometrically reduced at the image of `x`,
then `X` is geometrically reduced at `x`. -/
theorem geometricallyReducedAt_of_etaleAt_map {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} (f : X ⟶ Y) {x : Points X}
    (hf : EtaleAt f x) (hy : GeometricallyReducedAt Y (Points.map f x)) :
    GeometricallyReducedAt X x :=
  sorry

/-- If `f` is surjective étale and `X` is geometrically reduced, then `Y` is
geometrically reduced. -/
theorem geometricallyReduced_of_surjective_etale {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} (f : X ⟶ Y) [Etale f] [Surjective f]
    [GeometricallyReduced X] : GeometricallyReduced Y :=
  sorry

/-- If `f` is surjective étale and `Y` is geometrically reduced, then `X` is
geometrically reduced. -/
theorem geometricallyReduced_source_of_surjective_etale {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} (f : X ⟶ Y) [Etale f] [Surjective f]
    [GeometricallyReduced Y] : GeometricallyReduced X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
