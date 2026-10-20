/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineOpen
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability

/-!
# Finite locally free groupoid quotients

If the source and target of a groupoid scheme are finite locally free, the defining
map `(t, s)` is an equivalence relation, and every nonempty closed subset of the object
scheme meets an orbit contained in an affine open, then the fppf quotient is a scheme.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The orbit of a point is the image under the target map of the source fibre over it. -/
def orbit {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) : Set G.U.left :=
  G.t.left '' (G.s.left ⁻¹' {u})

/-- A point belongs to an orbit exactly when it is the target of an arrow from its base point. -/
theorem mem_orbit {S : Scheme.{u}} (G : GroupoidScheme S) {u v : G.U.left} :
    v ∈ G.orbit u ↔ ∃ r : G.R.left, G.s.left r = u ∧ G.t.left r = v := sorry

/-- The Fact packaging of the condition that every nonempty closed subset contains a point whose orbit is contained in an affine open. -/
abbrev HasAffineOrbitClosedPoint {S : Scheme.{u}} (G : GroupoidScheme S) : Prop :=
  Fact (∀ (Z : Set G.U.left), IsClosed Z → Z.Nonempty →
    ∃ u ∈ Z, ∃ W : G.U.left.affineOpens, G.orbit u ⊆ (W : Set G.U.left))

/-- The class `HasAffineOrbitClosedPoint` is equivalent to its quantified closed-set condition. -/
theorem hasAffineOrbitClosedPoint_iff {S : Scheme.{u}} (G : GroupoidScheme S) :
    HasAffineOrbitClosedPoint G ↔
      ∀ (Z : Set G.U.left), IsClosed Z → Z.Nonempty →
        ∃ u ∈ Z, ∃ W : G.U.left.affineOpens, G.orbit u ⊆ (W : Set G.U.left) := sorry

/-- An affine object scheme satisfies the affine-orbit closed-point condition. -/
theorem hasAffineOrbitClosedPoint_of_isAffine {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.U.left] : HasAffineOrbitClosedPoint G := sorry

/-- The affine-orbit closed-point condition follows when every point has affine-contained orbit. -/
theorem hasAffineOrbitClosedPoint_of_forall {S : Scheme.{u}} (G : GroupoidScheme S)
    (h : ∀ u : G.U.left, ∃ W : G.U.left.affineOpens,
      G.orbit u ⊆ (W : Set G.U.left)) :
    HasAffineOrbitClosedPoint G := sorry

/-- The affine-orbit closed-point condition follows when every finite type point has affine-contained orbit. -/
theorem hasAffineOrbitClosedPoint_of_finiteTypePoints {S : Scheme.{u}}
    (G : GroupoidScheme S)
    (h : ∀ u ∈ finiteTypePoints G.U.left, ∃ W : G.U.left.affineOpens,
      G.orbit u ⊆ (W : Set G.U.left)) :
    HasAffineOrbitClosedPoint G := sorry

/-- The affine-orbit closed-point condition follows from a specializing set of points with affine-contained orbits. -/
theorem hasAffineOrbitClosedPoint_of_specializes {S : Scheme.{u}}
    (G : GroupoidScheme S) {E : Set G.U.left}
    (hE : ∀ e ∈ E, ∃ W : G.U.left.affineOpens, G.orbit e ⊆ (W : Set G.U.left))
    (h : ∀ u : G.U.left, ∃ e ∈ E, Specializes u e) :
    HasAffineOrbitClosedPoint G := sorry

/-- A finite locally free equivalence relation where every nonempty closed subset
contains a point whose orbit is contained in an affine open has a finite locally free
scheme quotient representing its fppf quotient sheaf. -/
theorem exists_finiteLocallyFree_fppfQuotient {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] [HasAffineOrbitClosedPoint G] :
    ∃ (M : Over S) (q : G.U ⟶ M)
      (h : G.toPreRelation.t ≫ q = G.toPreRelation.s ≫ q),
      IsFiniteLocallyFree q.left ∧
        IsIso (G.toPreRelation.kernelPairLift q h) ∧
          IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _ G.toPreRelation
            (StandardTopology.fppf.overTopology S)
            (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
            q h) := sorry

/-- The fppf quotient sheaf is representable under the finite locally free quotient hypotheses. -/
theorem hasRepresentableQuotient_fppf {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] [HasAffineOrbitClosedPoint G] :
    HasRepresentableQuotient StandardTopology.fppf G := sorry

end AlgebraicGeometry.GroupoidScheme
