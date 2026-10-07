module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_33_1_ResidueFieldTrdeg
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite

/-!
# Quasi-finiteness over a point of codimension at most one

A locally finite-type morphism of algebraic spaces into a locally Noetherian
target is quasi-finite at every point lying over a point of codimension at most
one, under any of the four generically finite hypotheses of Stacks Lemma 72.3.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.3.1 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type and `Y` is
locally Noetherian. Let `y` be a point of `|Y|` of codimension `≤ 1`. If every
codimension-zero point `x` of `|X|` has residue-field transcendence degree of
`x / f(x)` equal to `0`, then `f` is quasi-finite at every point of `|X|`
lying over `y`. -/
@[stacks 0AD1]
theorem quasiFiniteAt_of_residueFieldTrdeg_eq_zero {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (htrdeg : ∀ x : Points X, localRingDimAt x = 0 → ResidueFieldTrdegEqAt f 0 x)
    {x : Points X} (hx : Points.map f x = y) : QuasiFiniteAt f x :=
  sorry

/-- Lemma 72.3.1 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type and `Y` is
locally Noetherian. Let `y` be a point of `|Y|` of codimension `≤ 1`. If every
codimension-zero point `x` of `|X|` with `f(x) ⤳ y` has residue-field
transcendence degree of `x / f(x)` equal to `0`, then `f` is quasi-finite at
every point of `|X|` lying over `y`. -/
@[stacks 0AD1]
theorem quasiFiniteAt_of_residueFieldTrdeg_eq_zero_of_specializes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y : Points Y}
    (hy : localRingDimAt y ≤ 1)
    (htrdeg : ∀ x : Points X, localRingDimAt x = 0 → Points.map f x ⤳ y →
      ResidueFieldTrdegEqAt f 0 x)
    {x : Points X} (hx : Points.map f x = y) : QuasiFiniteAt f x :=
  sorry

/-- Lemma 72.3.1 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type and `Y` is
locally Noetherian. Let `y` be a point of `|Y|` of codimension `≤ 1`. If `f`
is quasi-finite at every codimension-zero point of `|X|`, then `f` is
quasi-finite at every point of `|X|` lying over `y`. -/
@[stacks 0AD1]
theorem quasiFiniteAt_of_codimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y : Points Y}
    (hy : localRingDimAt y ≤ 1)
    (hqf : ∀ x : Points X, localRingDimAt x = 0 → QuasiFiniteAt f x)
    {x : Points X} (hx : Points.map f x = y) : QuasiFiniteAt f x :=
  sorry

/-- Lemma 72.3.1 (4): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type and `Y` is
locally Noetherian. Let `y` be a point of `|Y|` of codimension `≤ 1`. If `f`
is quasi-finite at a dense set of points of `|X|`, then `f` is quasi-finite at
every point of `|X|` lying over `y`. -/
@[stacks 0AD1]
theorem quasiFiniteAt_of_denseLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y : Points Y}
    (hy : localRingDimAt y ≤ 1)
    (hdense : Dense (setOf fun z : Points X ↦ QuasiFiniteAt f z))
    {x : Points X} (hx : Points.map f x = y) : QuasiFiniteAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
