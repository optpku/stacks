module

public import Mathlib.Topology.Spectral.Basic
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_4_6_Topology

/-!
# Spectral spaces of quasi-compact quasi-separated algebraic spaces

The space of points of a quasi-compact, absolutely quasi-separated algebraic space is spectral.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.15.2: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Then the topological space `Points X` is a spectral space. -/
@[stacks 0A4G]
instance instSpectralSpacePoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] : SpectralSpace (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
