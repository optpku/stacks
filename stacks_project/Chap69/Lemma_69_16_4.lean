module

public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap69.Lemma_69_16_4_ZeroLocus
public import stacks_project.Chap69.Situation_69_16_1

/-!
# Lemma 69.16.4

Disjoint closed subsets of an algebraic space with vanishing `H¹` on quasi-coherent modules
are separated by a global function and its translate by `1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.16.4: in Situation 69.16.1, if `Z₀` and `Z₁` are disjoint closed subsets of
`Points X`, then there exists `a : globalSectionsRing X` such that
`(Z₀ : Set (Points X)) ⊆ X.zeroLocus {a}` and
`(Z₁ : Set (Points X)) ⊆ X.zeroLocus {a - 1}`. -/
@[stacks 07V1]
theorem exists_zeroLocus_subset_of_disjoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] (Z₀ Z₁ : TopologicalSpace.Closeds (Points X))
    (hdisj : Disjoint (Z₀ : Set (Points X)) (Z₁ : Set (Points X))) :
    ∃ a : globalSectionsRing X,
      (Z₀ : Set (Points X)) ⊆ X.zeroLocus {a} ∧
        (Z₁ : Set (Points X)) ⊆ X.zeroLocus {a - 1} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
