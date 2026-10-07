module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Spectral.Basic
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Punctured generizations of points of decent locally Noetherian algebraic spaces

The punctured generization set of a point of a decent locally Noetherian algebraic space
is a Noetherian, spectral, sober, Jacobson topological space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

/-- The set of points of `X` that specialize to `x`, other than `x` itself. -/
def puncturedGenerizations {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    Set (Points X) :=
  {x' | x' ⤳ x ∧ x' ≠ x}

/-- A point lies in `puncturedGenerizations x` if and only if it specializes to `x` and is
distinct from `x`. -/
theorem mem_puncturedGenerizations {S : Scheme.{u}} {X : AlgebraicSpace S} {x x' : Points X} :
    x' ∈ puncturedGenerizations x ↔ x' ⤳ x ∧ x' ≠ x :=
  sorry

/-- Lemma 68.23.5 (1): Let `S` be a scheme. Let `X` be a decent locally Noetherian algebraic
space over `S`. Let `x ∈ Points X`. Then `W = {x' | x' ⤳ x ∧ x' ≠ x}` is a Noetherian
topological space. -/
@[stacks 0ED2]
instance instNoetherianSpace_puncturedGenerizations {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsLocallyNoetherian X] (x : Points X) :
    TopologicalSpace.NoetherianSpace (puncturedGenerizations x) :=
  sorry

/-- Lemma 68.23.5 (2): Let `S` be a scheme. Let `X` be a decent locally Noetherian algebraic
space over `S`. Let `x ∈ Points X`. Then `W = {x' | x' ⤳ x ∧ x' ≠ x}` is a spectral
topological space. -/
@[stacks 0ED2]
instance instSpectralSpace_puncturedGenerizations {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsLocallyNoetherian X] (x : Points X) :
    SpectralSpace (puncturedGenerizations x) :=
  sorry

/-- Lemma 68.23.5 (3): Let `S` be a scheme. Let `X` be a decent locally Noetherian algebraic
space over `S`. Let `x ∈ Points X`. Then `W = {x' | x' ⤳ x ∧ x' ≠ x}` is a sober
topological space. -/
@[stacks 0ED2]
theorem puncturedGenerizations_sober {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsLocallyNoetherian X] {x : Points X} :
    T0Space (puncturedGenerizations x) ∧ QuasiSober (puncturedGenerizations x) :=
  sorry

/-- Lemma 68.23.5 (4): Let `S` be a scheme. Let `X` be a decent locally Noetherian algebraic
space over `S`. Let `x ∈ Points X`. Then `W = {x' | x' ⤳ x ∧ x' ≠ x}` is a Jacobson
topological space. -/
@[stacks 0ED2]
instance instJacobsonSpace_puncturedGenerizations {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsLocallyNoetherian X] (x : Points X) :
    JacobsonSpace (puncturedGenerizations x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Points

