/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap79.Lemma_79_12_8_OfPoint

/-!
# Étale atlas of the finite-part functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/-- Lemma 79.12.10: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is separated and locally quasi-finite, then
there exists a scheme `U` étale over `Y` and a surjective étale morphism
`U ⟶ (X/Y)_fin` over `Y`. -/
@[stacks 04QG]
theorem exists_surjective_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicSpace.Separated f] [AlgebraicSpace.LocallyQuasiFinite f] :
    ∃ (U : Over S) (a : ofOver U ⟶ Y) (φ : yoneda.obj U ⟶ functor f),
      AlgebraicSpace.Etale a ∧ φ ≫ hom f = a ∧
        (over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf φ ∧
        (over (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).presheaf φ :=
  sorry

/-- A representably étale and surjective morphism `φ : U ⟶ (X/Y)_fin` is
étale-locally surjective. -/
theorem isLocallySurjective_of_surjective_etale
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {U : Over S}
    {φ : yoneda.obj U ⟶ functor f}
    (h_etale : (over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf φ)
    (h_surj : (over (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).presheaf φ) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
