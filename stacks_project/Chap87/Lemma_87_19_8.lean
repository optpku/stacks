/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_9_10_Map

/-!
# Morphisms of formal spectra representable by algebraic spaces

A continuous map of weakly admissible topological rings over a scheme `S`
induces a representable morphism of formal spectra if and only if it is taut.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
variable (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
variable [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- Lemma 87.19.8: Let `S` be a scheme. Let `φ : A →+* B` be a continuous map
of weakly admissible topological rings over `S`. The following are equivalent:
`spfMap φ : spf B hB ⟶ spf A hA` is representable by algebraic spaces,
`spfMap φ` is representable by schemes, and `φ` is taut. -/
@[stacks 0AN5]
theorem spfMap_tfae :
    List.TFAE
      [AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)),
        yoneda.relativelyRepresentable
          ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)),
        φ.IsTaut] :=
  sorry

/-- `spfMap φ` is representable by algebraic spaces if and only if it is
representable by schemes. -/
theorem spfMap_representableByAlgebraicSpaces_iff_relativelyRepresentable :
    AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)) ↔
      yoneda.relativelyRepresentable
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)) :=
  sorry

/-- `spfMap φ` is representable by algebraic spaces if and only if `φ` is taut. -/
theorem spfMap_representableByAlgebraicSpaces_iff_isTaut :
    AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)) ↔
      φ.IsTaut :=
  sorry

/-- `spfMap φ` is representable by schemes if and only if `φ` is taut. -/
theorem spfMap_relativelyRepresentable_iff_isTaut :
    yoneda.relativelyRepresentable
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)) ↔
      φ.IsTaut :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
