module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Topology.QuasiSeparated
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus

/-!
# Dense schematic locus from a finite étale quasi-separated scheme cover

A finite étale surjective morphism from a quasi-separated scheme onto an algebraic
space forces the schematic locus to contain every codimension-zero point, hence to
be a dense open subspace which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- Lemma 66.13.2 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If there exists a finite, étale, surjective morphism `U ⟶ X` where `U` is a
quasi-separated scheme, then there exists a dense open subspace of `X` which is a
scheme. -/
@[stacks 0BAS]
theorem exists_dense_open_isScheme_of_finiteEtale (f : ofOver U ⟶ X)
    (hf_finite : (MorphismProperty.over (@AlgebraicGeometry.IsFinite)).presheaf f)
    (hf_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (hf_surj : (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f)
    [QuasiSeparatedSpace U.left] :
    ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet :=
  sorry

/-- Lemma 66.13.2 (2): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If there exists a finite, étale, surjective morphism `U ⟶ X` where `U` is a
quasi-separated scheme, then every point of `Points X` of codimension `0` in `X`
is contained in `schematicLocus X`. -/
@[stacks 0BAS]
theorem codimZero_subset_schematicLocus_of_finiteEtale (f : ofOver U ⟶ X)
    (hf_finite : (MorphismProperty.over (@AlgebraicGeometry.IsFinite)).presheaf f)
    (hf_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (hf_surj : (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f)
    [QuasiSeparatedSpace U.left] :
    (setOf fun x : Points X ↦ localRingDimAt x = 0) ⊆ (schematicLocus X).pointsSet :=
  sorry

/-- A finite étale surjective morphism from a quasi-separated scheme makes the
schematic locus of `X` dense in `Points X`. -/
theorem dense_schematicLocus_of_finiteEtale (f : ofOver U ⟶ X)
    (hf_finite : (MorphismProperty.over (@AlgebraicGeometry.IsFinite)).presheaf f)
    (hf_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (hf_surj : (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f)
    [QuasiSeparatedSpace U.left] :
    Dense (schematicLocus X).pointsSet :=
  sorry

/-- A finite étale surjective morphism from a quasi-separated scheme places every
codimension-zero point of `X` in the schematic locus. -/
theorem mem_schematicLocus_of_localRingDimAt_eq_zero (f : ofOver U ⟶ X)
    (hf_finite : (MorphismProperty.over (@AlgebraicGeometry.IsFinite)).presheaf f)
    (hf_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (hf_surj : (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f)
    [QuasiSeparatedSpace U.left] {x : Points X} (hx : localRingDimAt x = 0) :
    x ∈ (schematicLocus X).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
