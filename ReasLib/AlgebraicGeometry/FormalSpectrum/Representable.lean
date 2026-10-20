module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
public import ReasLib.Topology.Algebra.Ring.Taut
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Data.List.TFAE

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

/-- Let `S` be a scheme. Let `φ : A →+* B` be a continuous map
of weakly admissible topological rings over `S`. The following are equivalent:
`spfMap φ : spf B hB ⟶ spf A hA` is representable by algebraic spaces,
`spfMap φ` is representable by schemes, and `φ` is taut. -/
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
  (spfMap_tfae hA hB φ hφ h_over).out 0 1

/-- `spfMap φ` is representable by algebraic spaces if and only if `φ` is taut. -/
theorem spfMap_representableByAlgebraicSpaces_iff_isTaut :
    AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)) ↔
      φ.IsTaut :=
  (spfMap_tfae hA hB φ hφ h_over).out 0 2

/-- `spfMap φ` is representable by schemes if and only if `φ` is taut. -/
theorem spfMap_relativelyRepresentable_iff_isTaut :
    yoneda.relativelyRepresentable
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)) ↔
      φ.IsTaut :=
  (spfMap_tfae hA hB φ hφ h_over).out 1 2

end AlgebraicGeometry.AffineFormalAlgebraicSpace
