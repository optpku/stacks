/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_9_10_Map
public import stacks_project.Chap87.Lemma_87_24_4_FiniteType

/-!
# Finite type morphisms of formal spectra

A continuous map of weakly admissible topological rings over a scheme `S`
induces a finite type morphism of formal spectra if and only if it is taut
and topologically of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
variable (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
variable [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- Lemma 87.29.2: Let `S` be a scheme. Let `φ : A →+* B` be a continuous map
of weakly admissible topological rings over `S`. Then
`spfMap φ : spf B hB ⟶ spf A hA` is of finite type if and only if `φ` is taut
and `B` is topologically of finite type over `A`. -/
@[stacks 0ANT]
theorem spfMap_finiteType_iff :
    FiniteType
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
          (spfMap φ hφ h_over)) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  sorry

/-- If `φ` is taut and topologically of finite type, then `spfMap φ` is of
finite type. -/
theorem spfMap_finiteType_of_isTaut_and_topologicallyOfFiniteType
    (h_taut : φ.IsTaut) (h_tft : φ.TopologicallyOfFiniteType) :
    FiniteType
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap φ hφ h_over)) :=
  sorry

/-- If `spfMap φ` is of finite type, then `φ` is taut and topologically of
finite type. -/
theorem isTaut_and_topologicallyOfFiniteType_of_spfMap_finiteType
    (h : FiniteType
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap φ hφ h_over))) :
    φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
