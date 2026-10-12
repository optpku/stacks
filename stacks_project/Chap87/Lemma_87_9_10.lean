/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_9_10_Map

/-!
# Morphisms between formal spectra

A morphism of affine formal algebraic spaces `spf B hB ⟶ spf A hA` over `S`
is uniquely of the form `spfMap φ` for a continuous `S`-algebra map
`φ : A →+* B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- Lemma 87.9.10: Let `S` be a scheme. Let `A`, `B` be weakly admissible
topological rings over `S`. Any morphism `f : spf B hB ⟶ spf A hA` of affine
formal algebraic spaces over `S` is equal to `spfMap φ hφ h_over` for a unique
continuous `S`-algebra map `φ : A →+* B`. -/
@[stacks 0AN0]
theorem existsUnique_eq_spfMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (f : spf B hB ⟶ spf A hA) :
    ∃! φ : A →+* B, ∃ (hφ : Continuous φ)
      (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB),
      f = spfMap φ hφ h_over :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
