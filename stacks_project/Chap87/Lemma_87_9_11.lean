/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap88.Definition_88_18_1_Affine

/-!
# Affine formal algebraic spaces and locally quasi-finite maps

A map of presheaves on schemes over `S` with affine formal algebraic space
source that is representable by algebraic spaces and locally quasi-finite is
representable by schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.9.11: let `S` be a scheme. Let `f : X ⟶ Y` be a map of presheaves
on `(Sch/S)_fppf`. If `X` is an affine formal algebraic space, including the
coequalizer size condition of Definition 87.9.1, and `f` is representable by
algebraic spaces and locally quasi-finite, then `f` is representable by
schemes, in the sense of `yoneda.relativelyRepresentable`. -/
@[stacks 0AIG]
theorem relativelyRepresentable_of_locallyQuasiFinite
    {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) [IsAffine X]
    (h_presentation :
      ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)
    (hf : representableByAlgebraicSpaces f)
    (h_locallyOfFiniteType :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y), AlgebraicSpace.LocallyOfFiniteType (hf.pullbackHom ξ))
    (h_locallyQuasiFinite :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y), AlgebraicSpace.LocallyQuasiFinite (hf.pullbackHom ξ)) :
    yoneda.relativelyRepresentable f :=
  sorry

/-- The fibre product algebraic space of a locally quasi-finite morphism from an
affine formal algebraic space along a Yoneda section is a scheme. -/
theorem isScheme_pullbackSpace {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [IsAffine X]
    (h_presentation :
      ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)
    (hf : representableByAlgebraicSpaces f)
    (h_locallyOfFiniteType :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y), AlgebraicSpace.LocallyOfFiniteType (hf.pullbackHom ξ))
    (h_locallyQuasiFinite :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y), AlgebraicSpace.LocallyQuasiFinite (hf.pullbackHom ξ))
    ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y) :
    AlgebraicSpace.IsScheme (hf.pullbackSpace ξ) :=
  sorry

/-- Each Yoneda pullback of a locally quasi-finite morphism from an affine
formal algebraic space is a representable functor. -/
theorem isRepresentable_pullback {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [IsAffine X]
    (h_presentation :
      ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)
    (hf : representableByAlgebraicSpaces f)
    (h_locallyOfFiniteType :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y), AlgebraicSpace.LocallyOfFiniteType (hf.pullbackHom ξ))
    (h_locallyQuasiFinite :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y), AlgebraicSpace.LocallyQuasiFinite (hf.pullbackHom ξ))
    ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y) :
    (pullback ξ f).IsRepresentable :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
