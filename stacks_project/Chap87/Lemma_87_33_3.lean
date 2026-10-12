/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReasLib.RingTheory.Completion.LocalRing
public import stacks_project.Chap87.Lemma_87_33_3_Comparison

/-!
# Maps out of affine formal schemes, algebraic-space targets

For a complete local Noetherian `S`-algebra `R` and an algebraic space `X` over
`S`, morphisms `Spec(R) ⟶ X` over `S` are in bijection with morphisms
`Spf(R) ⟶ X` over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- Lemma 87.33.3: Let `S` be a scheme. Let `R` be a complete local Noetherian
`S`-algebra. Let `X` be an algebraic space over `S`. Then the natural map
`Mor_S(Spec(R), X) ⟶ Mor_S(Spf(R), X)` is bijective. -/
@[stacks 0AQH]
theorem specHomToSpfHom_algebraicSpace_bijective {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsNoetherianRing R] [IsCompleteLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (X : AlgebraicSpace S) :
    Function.Bijective (specHomToSpfHom_algebraicSpace structureHom X) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
