/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational.Proper

/-!
# Isomorphism loci of proper birational morphisms

A proper birational morphism of algebraic spaces into a Noetherian target, with
reduced source, is an isomorphism over every codimension-zero point, every
normal codimension-one point, and every normal point with finite fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.3.3 (1): Let `S` be a scheme. Let `X` be a Noetherian algebraic
space over `S`. Let `f : Y ⟶ X` be a birational proper morphism of algebraic
spaces with `Y` reduced. Let `U ⊂ X` be the maximal open over which `f` is an
isomorphism, recorded as `isomorphismLocus f`. Then `U` contains every point of
codimension `0` in `X`. -/
@[stacks 0BBQ] #check (AlgebraicGeometry.AlgebraicSpace.mem_isomorphismLocus_of_localRingDimAt_eq_zero :
  ∀
    {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsDecent Y] [IsDecent X]
    [HasFiniteIrreducibleComponents Y] [HasFiniteIrreducibleComponents X]
    [IsNoetherian X] [IsReduced Y] (f : Y ⟶ X) [IsBirational f] [Proper f]
    {x : Points X} (hx : localRingDimAt x = 0),
    x ∈ isomorphismLocus f)

/- Lemma 72.3.3 (2): Let `S` be a scheme. Let `X` be a Noetherian algebraic
space over `S`. Let `f : Y ⟶ X` be a birational proper morphism of algebraic
spaces with `Y` reduced. Let `U ⊂ X` be the maximal open over which `f` is an
isomorphism, recorded as `isomorphismLocus f`. Then `U` contains every
`x ∈ |X|` of codimension `1` on `X` such that the local ring of `X` at `x` is
normal, in the sense of `localRingHas (fun R ↦ IsNormalRing R)` from Remark
66.7.6. -/
@[stacks 0BBQ] #check (AlgebraicGeometry.AlgebraicSpace.mem_isomorphismLocus_of_localRingDimAt_eq_one_of_normal :
  ∀
    {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsDecent Y] [IsDecent X]
    [HasFiniteIrreducibleComponents Y] [HasFiniteIrreducibleComponents X]
    [IsNoetherian X] [IsReduced Y] (f : Y ⟶ X) [IsBirational f] [Proper f]
    {x : Points X} (hx : localRingDimAt x = 1)
    (hN : localRingHas (fun R ↦ IsNormalRing R) X x),
    x ∈ isomorphismLocus f)

/- Lemma 72.3.3 (3): Let `S` be a scheme. Let `X` be a Noetherian algebraic
space over `S`. Let `f : Y ⟶ X` be a birational proper morphism of algebraic
spaces with `Y` reduced. Let `U ⊂ X` be the maximal open over which `f` is an
isomorphism, recorded as `isomorphismLocus f`. Then `U` contains every
`x ∈ |X|` such that the fibre of `|Y| ⟶ |X|` over `x` is finite and such that
the local ring of `X` at `x` is normal, in the sense of
`localRingHas (fun R ↦ IsNormalRing R)` from Remark 66.7.6. -/
@[stacks 0BBQ] #check (AlgebraicGeometry.AlgebraicSpace.mem_isomorphismLocus_of_finite_fiberOver_of_normal :
  ∀
    {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsDecent Y] [IsDecent X]
    [HasFiniteIrreducibleComponents Y] [HasFiniteIrreducibleComponents X]
    [IsNoetherian X] [IsReduced Y] (f : Y ⟶ X) [IsBirational f] [Proper f]
    {x : Points X} (hfin : (fiberOver f x).Finite)
    (hN : localRingHas (fun R ↦ IsNormalRing R) X x),
    x ∈ isomorphismLocus f)

end AlgebraicGeometry.AlgebraicSpace
