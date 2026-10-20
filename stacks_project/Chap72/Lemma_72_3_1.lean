/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.GenericPoints

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.3.1 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type and `Y` is
locally Noetherian. Let `y` be a point of `|Y|` of codimension `≤ 1`. If every
codimension-zero point `x` of `|X|` has residue-field transcendence degree of
`x / f(x)` equal to `0`, then `f` is quasi-finite at every point of `|X|`
lying over `y`. -/
@[stacks 0AD1] #check (AlgebraicGeometry.AlgebraicSpace.quasiFiniteAt_of_residueFieldTrdeg_eq_zero :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (htrdeg : ∀ x : Points X, localRingDimAt x = 0 → ResidueFieldTrdegEqAt f 0 x)
    {x : Points X} (hx : Points.map f x = y), QuasiFiniteAt f x)

/- Lemma 72.3.1 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type and `Y` is
locally Noetherian. Let `y` be a point of `|Y|` of codimension `≤ 1`. If every
codimension-zero point `x` of `|X|` with `f(x) ⤳ y` has residue-field
transcendence degree of `x / f(x)` equal to `0`, then `f` is quasi-finite at
every point of `|X|` lying over `y`. -/
@[stacks 0AD1] #check (AlgebraicGeometry.AlgebraicSpace.quasiFiniteAt_of_residueFieldTrdeg_eq_zero_of_specializes :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y : Points Y}
    (hy : localRingDimAt y ≤ 1)
    (htrdeg : ∀ x : Points X, localRingDimAt x = 0 → Points.map f x ⤳ y →
      ResidueFieldTrdegEqAt f 0 x)
    {x : Points X} (hx : Points.map f x = y), QuasiFiniteAt f x)

/- Lemma 72.3.1 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type and `Y` is
locally Noetherian. Let `y` be a point of `|Y|` of codimension `≤ 1`. If `f`
is quasi-finite at every codimension-zero point of `|X|`, then `f` is
quasi-finite at every point of `|X|` lying over `y`. -/
@[stacks 0AD1] #check (AlgebraicGeometry.AlgebraicSpace.quasiFiniteAt_of_codimZero :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y : Points Y}
    (hy : localRingDimAt y ≤ 1)
    (hqf : ∀ x : Points X, localRingDimAt x = 0 → QuasiFiniteAt f x)
    {x : Points X} (hx : Points.map f x = y), QuasiFiniteAt f x)

/- Lemma 72.3.1 (4): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type and `Y` is
locally Noetherian. Let `y` be a point of `|Y|` of codimension `≤ 1`. If `f`
is quasi-finite at a dense set of points of `|X|`, then `f` is quasi-finite at
every point of `|X|` lying over `y`. -/
@[stacks 0AD1] #check (AlgebraicGeometry.AlgebraicSpace.quasiFiniteAt_of_denseLocus :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y : Points Y}
    (hy : localRingDimAt y ≤ 1)
    (hdense : Dense (setOf fun z : Points X ↦ QuasiFiniteAt f z))
    {x : Points X} (hx : Points.map f x = y), QuasiFiniteAt f x)

end AlgebraicGeometry.AlgebraicSpace
