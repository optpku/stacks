module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage

/-!
# Finite neighbourhoods in codimension at most one

A proper morphism of algebraic spaces into a locally Noetherian target is
finite over an open neighbourhood of a point of codimension at most one if
residue-field transcendence degrees vanish at the relevant codimension-zero
points, if it is quasi-finite at all codimension-zero points, or if its
quasi-finite locus is dense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is proper and `Y` is locally Noetherian.
Let `y` be a point of `|Y|` of codimension `≤ 1`. If every codimension-zero
point `x` of `|X|` has residue-field transcendence degree of `x / f(x)` equal
to `0`, then there exists an open subspace `Y' ⊂ Y` containing `y` such that
`Y' ×_Y X ⟶ Y'` is finite.

The open subspace is an open immersion `ι : Y' ⟶ Y` with
`y ∈ Set.range (Points.map ι)`, and the restricted morphism is
`openInverseImageTo f ι : openInverseImage f ι ⟶ Y'`. -/
@[stacks 0AD2]
theorem exists_isFinite_openInverseImageTo_of_residueFieldTrdeg_eq_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (htrdeg : ∀ x : Points X, localRingDimAt x = 0 → ResidueFieldTrdegEqAt f 0 x) :
    ∃ (Y' : AlgebraicSpace S) (ι : Y' ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι) :=
  sorry

namespace IsFinite

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is proper and `Y` is locally Noetherian.
Let `y` be a point of `|Y|` of codimension `≤ 1`. If every codimension-zero
point `x` of `|X|` with `f(x) ⤳ y` has residue-field transcendence degree of
`x / f(x)` equal to `0`, then there exists an open subspace `Y' ⊂ Y`
containing `y` such that `Y' ×_Y X ⟶ Y'` is finite.

The open subspace is an open immersion `ι : Y' ⟶ Y` with
`y ∈ Set.range (Points.map ι)`, and the restricted morphism is
`openInverseImageTo f ι : openInverseImage f ι ⟶ Y'`. -/
theorem exists_open_of_trdeg_eq_zero_of_specializes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (htrdeg : ∀ x : Points X, localRingDimAt x = 0 → Points.map f x ⤳ y →
      ResidueFieldTrdegEqAt f 0 x) :
    ∃ (Y' : AlgebraicSpace S) (ι : Y' ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι) :=
  sorry

end IsFinite

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is proper and `Y` is locally Noetherian.
Let `y` be a point of `|Y|` of codimension `≤ 1`. If `f` is quasi-finite at
every codimension-zero point of `|X|`, then there exists an open subspace
`Y' ⊂ Y` containing `y` such that `Y' ×_Y X ⟶ Y'` is finite.

The open subspace is an open immersion `ι : Y' ⟶ Y` with
`y ∈ Set.range (Points.map ι)`, and the restricted morphism is
`openInverseImageTo f ι : openInverseImage f ι ⟶ Y'`. -/
@[stacks 0AD2]
theorem exists_isFinite_openInverseImageTo_of_codimZero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (hqf : ∀ x : Points X, localRingDimAt x = 0 → QuasiFiniteAt f x) :
    ∃ (Y' : AlgebraicSpace S) (ι : Y' ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι) :=
  sorry

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is proper and `Y` is locally Noetherian.
Let `y` be a point of `|Y|` of codimension `≤ 1`. If `f` is quasi-finite at a
dense set of points of `|X|`, then there exists an open subspace `Y' ⊂ Y`
containing `y` such that `Y' ×_Y X ⟶ Y'` is finite.

The open subspace is an open immersion `ι : Y' ⟶ Y` with
`y ∈ Set.range (Points.map ι)`, and the restricted morphism is
`openInverseImageTo f ι : openInverseImage f ι ⟶ Y'`. -/
@[stacks 0AD2]
theorem exists_isFinite_openInverseImageTo_of_denseLocus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (hdense : Dense (setOf fun z : Points X ↦ QuasiFiniteAt f z)) :
    ∃ (Y' : AlgebraicSpace S) (ι : Y' ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
