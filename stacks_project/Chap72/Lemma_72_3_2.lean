/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_33_1_ResidueFieldTrdeg
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite

/-!
# Finite neighbourhoods in codimension at most one

A proper morphism of algebraic spaces into a locally Noetherian target is
finite over some open neighbourhood of a point of codimension at most one,
under any of the four generically finite hypotheses of Stacks Lemma 72.3.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.3.2 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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

/-- Lemma 72.3.2 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is proper and `Y` is locally Noetherian.
Let `y` be a point of `|Y|` of codimension `≤ 1`. If every codimension-zero
point `x` of `|X|` with `f(x) ⤳ y` has residue-field transcendence degree of
`x / f(x)` equal to `0`, then there exists an open subspace `Y' ⊂ Y`
containing `y` such that `Y' ×_Y X ⟶ Y'` is finite.

The open subspace is an open immersion `ι : Y' ⟶ Y` with
`y ∈ Set.range (Points.map ι)`, and the restricted morphism is
`openInverseImageTo f ι : openInverseImage f ι ⟶ Y'`. -/
@[stacks 0AD2]
theorem exists_isFinite_openInverseImageTo_of_residueFieldTrdeg_eq_zero_of_specializes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (htrdeg : ∀ x : Points X, localRingDimAt x = 0 → Points.map f x ⤳ y →
      ResidueFieldTrdegEqAt f 0 x) :
    ∃ (Y' : AlgebraicSpace S) (ι : Y' ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι) :=
  sorry

/-- Lemma 72.3.2 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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

/-- Lemma 72.3.2 (4): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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
