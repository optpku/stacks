module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.FiniteEtale
import StacksCheckRecall

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

/- Lemma 66.13.2: Let S be a scheme. Let X be an algebraic space over S.
If there exists a finite, étale, surjective morphism U → X where U is a
quasi-separated scheme, then there exists a dense open subspace X' of X which
is a scheme. More precisely, every point x of codimension 0 in X is contained
in X'. -/
@[stacks 0BAS]
#check (AlgebraicGeometry.AlgebraicSpace.exists_dense_open_isScheme_of_finiteEtale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ X)
    (hf_finite : (MorphismProperty.over (@AlgebraicGeometry.IsFinite)).presheaf f)
    (hf_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (hf_surj : (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f)
    [QuasiSeparatedSpace U.left],
    ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet ∧
      ∀ x : Points X, localRingDimAt x = 0 → x ∈ X'.pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.codimZero_subset_schematicLocus_of_finiteEtale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ X)
    (hf_finite : (MorphismProperty.over (@AlgebraicGeometry.IsFinite)).presheaf f)
    (hf_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (hf_surj : (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f)
    [QuasiSeparatedSpace U.left],
    (setOf fun x : Points X ↦ localRingDimAt x = 0) ⊆ (schematicLocus X).pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.dense_schematicLocus_of_finiteEtaleCover :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} [IsScheme U] (f : U ⟶ X)
    [IsFinite f] [Etale f] [Surjective f], Dense (schematicLocus X).pointsSet)

end AlgebraicGeometry.AlgebraicSpace
