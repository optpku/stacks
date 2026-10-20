/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.Algebra.Polynomial.ArtinSchreier
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.ZMod

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.AffineLine

/-- The affine line over the spectrum of a commutative ring. -/
abbrev scheme (R : Type u) [CommRing R] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of R))

/-- The morphism of affine lines induced by an extension of fields. -/
def mapOfAlgebra (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    scheme k' ⟶ scheme k :=
  AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom (algebraMap k k')))

/-- Over an algebraically closed field of prime characteristic `p`, the first small-étale
cohomology group of the affine line with constant `ZMod p` coefficients is isomorphic
to the additive cokernel of the polynomial Artin–Schreier operator. -/
theorem h1_isIsomorphic_artinSchreierCoker
    (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    IsIsomorphic
      ((Sheaf.functorH (scheme k).smallEtaleTopology 1).obj
        (CategoryTheory.constantZModSheaf.{_, _, u} (scheme k).smallEtaleTopology p))
      (AddCommGrpCat.of (Polynomial.artinSchreierCoker p k)) := sorry

/-- A nonsurjective extension of algebraically closed fields in prime characteristic `p`
induces a noninvertible pullback on the first small-étale cohomology of affine lines
with constant `ZMod p` coefficients. -/
theorem h1_baseChange_not_isIso
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    [Algebra k k'] (p : ℕ) [Fact p.Prime] [CharP k p]
    (h_ne : ¬ Function.Surjective (algebraMap k k')) :
    ¬ IsIso
      (AlgebraicGeometry.Scheme.Hom.etaleHq_constant_pullback (mapOfAlgebra k k')
        (AddCommGrpCat.of (ULift.{u} (ZMod p))) 1) := sorry

/-- A nonsurjective extension of algebraically closed fields of prime positive characteristic
induces a nonbijective homomorphism on the geometric fundamental groups of the affine lines. -/
theorem pi1_map_not_bijective
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    [Algebra k k'] (p : ℕ) [Fact p.Prime] [CharP k p]
    [ConnectedSpace (scheme k)] [ConnectedSpace (scheme k')]
    (xbar : GeometricPoint (scheme k'))
    (h_ne : ¬ Function.Surjective (algebraMap k k')) :
    ¬ Function.Bijective
      (AlgebraicGeometry.Scheme.GeometricPoint.fundamentalGroupMap
        (mapOfAlgebra k k') xbar) := sorry

end AlgebraicGeometry.Etale.AffineLine
