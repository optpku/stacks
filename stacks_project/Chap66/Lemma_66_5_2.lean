module

public import Mathlib.Topology.Defs.Filter
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Quasi-compact algebraic spaces and compact points

An algebraic space over a scheme is quasi-compact if and only if its space of points
is quasi-compact for the topology presented by an open-quotient étale atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.5.2: let `S` be a scheme. Let `X` be an algebraic space over `S`. Then `X` is
quasi-compact if and only if `|X|` is quasi-compact. -/
@[stacks 03E4]
theorem isQuasiCompact_iff_compactSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    (τ : TopologicalSpace (Points X)) (A : Points.OpenQuotientAtlas X τ) :
    IsQuasiCompact X ↔ @CompactSpace (Points X) τ := sorry

/-- If `|X|` is quasi-compact for the topology presented by an open-quotient étale atlas,
then the algebraic space `X` is quasi-compact. -/
theorem isQuasiCompact_of_compactSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    (τ : TopologicalSpace (Points X)) (A : Points.OpenQuotientAtlas X τ)
    (h : @CompactSpace (Points X) τ) : IsQuasiCompact X := sorry

/-- If the algebraic space `X` is quasi-compact, then `|X|` is quasi-compact for the
topology presented by an open-quotient étale atlas. -/
theorem compactSpace_of_isQuasiCompact {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] (τ : TopologicalSpace (Points X))
    (A : Points.OpenQuotientAtlas X τ) : @CompactSpace (Points X) τ := sorry

end AlgebraicGeometry.AlgebraicSpace
