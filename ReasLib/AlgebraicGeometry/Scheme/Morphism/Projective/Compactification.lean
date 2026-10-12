/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Constructors
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.DimensionOne
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Nagata.EmptyFiber

/-!
# Compactifications of one-dimensional schemes

This file records projective compactifications of separated finite-type schemes of dimension at
most one over a field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.HProjective

/-- Every separated finite-type scheme over a field whose topological Krull dimension is at most
one admits an open immersion into an H-projective scheme over the field. Its image is dense and
scheme-theoretically dense, and its complement is a finite set of closed points. -/
theorem exists_compactification_of_dimension_le_one
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Scheme.Hom.FiniteType f] [IsSeparated f] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Xbar : Scheme.{u}) (fbar : Xbar ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Xbar)
      (hj : IsOpenImmersion j),
      let U : Xbar.Opens := @Scheme.Hom.opensRange _ _ j hj
      j ≫ fbar = f ∧
        HProjective fbar ∧
        Dense (U : Set Xbar) ∧
        schemeTheoreticallyDense U ∧
        Set.Finite ((U : Set Xbar)ᶜ) ∧
        ∀ x ∈ ((U : Set Xbar)ᶜ), x ∈ closedPoints Xbar := sorry

/-- Every reduced separated finite-type scheme over a field whose topological Krull dimension is
at most one admits an open immersion into an H-projective scheme over the field. Its image is
dense and scheme-theoretically dense, its complement is a finite set of closed points, and every
boundary stalk is a discrete valuation ring. -/
theorem exists_compactification_with_dvr_boundary_of_dimension_le_one
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Scheme.Hom.FiniteType f] [IsSeparated f] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Xbar : Scheme.{u}) (fbar : Xbar ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Xbar)
      (hj : IsOpenImmersion j),
      let U : Xbar.Opens := @Scheme.Hom.opensRange _ _ j hj
      j ≫ fbar = f ∧
        HProjective fbar ∧
        Dense (U : Set Xbar) ∧
        schemeTheoreticallyDense U ∧
        Set.Finite ((U : Set Xbar)ᶜ) ∧
        ∀ x ∈ ((U : Set Xbar)ᶜ),
          x ∈ closedPoints Xbar ∧
            ∃ (_ : IsDomain (Xbar.presheaf.stalk x)),
              IsDiscreteValuationRing (Xbar.presheaf.stalk x) := sorry

end AlgebraicGeometry.HProjective
