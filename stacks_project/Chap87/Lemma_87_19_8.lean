module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Representable
import StacksCheckRecall

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

/- Lemma 87.19.8: For a continuous map of weakly admissible topological rings
 over a scheme, representability of the induced formal-spectrum morphism by
 algebraic spaces, representability by schemes, and tautness are equivalent. -/
@[stacks 0AN5] #check (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfMap_tfae :
  ∀ {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
    List.TFAE
      [AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)),
        yoneda.relativelyRepresentable
          ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)),
        φ.IsTaut])

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfMap_representableByAlgebraicSpaces_iff_relativelyRepresentable :
  ∀ {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
    AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)) ↔
      yoneda.relativelyRepresentable
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfMap_representableByAlgebraicSpaces_iff_isTaut :
  ∀ {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
    AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)) ↔
      φ.IsTaut)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfMap_relativelyRepresentable_iff_isTaut :
  ∀ {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
    yoneda.relativelyRepresentable
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)) ↔
      φ.IsTaut)

end AlgebraicGeometry.AffineFormalAlgebraicSpace
