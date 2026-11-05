/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.ScalarChange
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Localization

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open scoped TensorProduct

noncomputable section

universe u

namespace CanonicalRingDeterminant

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Actual termwise scalar extension of a finite-projective representative. -/
def extendedModel (σ : R →+* S) (P : Model R) : Model S where
  complex := ((ModuleCat.extendScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.complex
  ge := by sorry
  le := by sorry
  finiteNeg := by sorry
  projectiveNeg := by sorry
  finiteZero := by sorry
  projectiveZero := by sorry

/-- Perfectness and Tor amplitude are preserved by derived scalar extension. -/
def extendedObject (σ : R →+* S) (K : Object R) : Object S :=
  ⟨⟨(ModuleCat.derivedExtensionOfScalars σ).obj K.obj.obj, by sorry⟩, by sorry⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The specified derived-to-underived counit is invertible on the bounded
projective representative; no arbitrary derived comparison is chosen. -/
instance representativeCounit_isIso (σ : R →+* S) (P : Model R) :
    IsIso ((ModuleCat.derivedExtensionComplexCounit σ).app P.complex) := by
  haveI (n : ℤ) : Projective (P.complex.X n) := by
    by_cases hneg : n = -1
    · subst n
      infer_instance
    by_cases hzero : n = 0
    · subst n
      infer_instance
    by_cases hn : n < -1
    · exact (P.complex.isZero_of_isStrictlyGE (-1) n hn).projective
    · exact (P.complex.isZero_of_isStrictlyLE 0 n (by omega)).projective
  letI : P.complex.IsKProjective := CochainComplex.isKProjective_of_projective P.complex 0
  let X := (HomotopyCategory.quotient (ModuleCat R) (up ℤ)).obj P.complex
  let hQ := CochainComplex.IsKProjective.fullyFaithfulFrom DerivedCategory.Qh P.complex
  let hi : IsInitial (StructuredArrow.mk (𝟙 (DerivedCategory.Qh.obj X))) :=
    IsInitial.ofUniqueHom
      (fun j ↦ StructuredArrow.homMk (hQ.preimage j.hom) (by
        change 𝟙 _ ≫ DerivedCategory.Qh.map (hQ.preimage j.hom) = j.hom
        rw [Category.id_comp, hQ.map_preimage]))
      (fun j f ↦ by
        apply StructuredArrow.hom_ext
        apply hQ.homEquiv.injective
        change DerivedCategory.Qh.map f.right = DerivedCategory.Qh.map (hQ.preimage j.hom)
        rw [hQ.map_preimage]
        have hf := StructuredArrow.w f
        change 𝟙 _ ≫ DerivedCategory.Qh.map f.right = j.hom at hf
        simpa only [Category.id_comp] using hf)
  haveI : IsIso ((ModuleCat.derivedExtensionOfScalarsCounit σ).app X) := by
    let h := (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
      (F' := ModuleCat.derivedExtensionOfScalars σ)
      (F := ModuleCat.extendScalarsToDerived σ)
      (L := DerivedCategory.Qh)
      (α := ModuleCat.derivedExtensionOfScalarsCounit σ)
      (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ))) (DerivedCategory.Qh.obj X)
    have hh := h.isIso_π_app_of_isInitial _ hi
    change IsIso ((ModuleCat.derivedExtensionOfScalars σ).map (𝟙 _) ≫
      (ModuleCat.derivedExtensionOfScalarsCounit σ).app X) at hh
    letI := hh
    exact IsIso.of_isIso_comp_left
      ((ModuleCat.derivedExtensionOfScalars σ).map (𝟙 (DerivedCategory.Qh.obj X)))
      ((ModuleCat.derivedExtensionOfScalarsCounit σ).app X)
  change IsIso
    ((Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat R))
        (ModuleCat.derivedExtensionOfScalars σ)).inv.app P.complex ≫
      (Functor.associator (HomotopyCategory.quotient (ModuleCat R) (up ℤ))
        DerivedCategory.Qh (ModuleCat.derivedExtensionOfScalars σ)).inv.app P.complex ≫
      (ModuleCat.derivedExtensionOfScalarsCounit σ).app X ≫
      (Functor.Homotopy.cochainIso (ModuleCat.extendScalars σ)).hom.app P.complex)
  infer_instance

def extendedRealization (σ : R →+* S) (K : Object R) :
    (extendedObject σ K).obj.obj ≅ DerivedCategory.Q.obj (extendedModel σ (model R K)).complex := by
  let e := @asIso _ _ _ _
    ((ModuleCat.derivedExtensionComplexCounit σ).app (model R K).complex)
    (representativeCounit_isIso σ (model R K))
  exact (ModuleCat.derivedExtensionOfScalars σ).mapIso (realization R K) ≪≫ e

/-- Identity on tensor representatives, isolating the bundled scalar actions
before applying exterior algebras. -/
def extendedTermEquiv (σ : R →+* S) (M : ModuleCat R) :
    -- Local instance justification (defeq pin): this tensor uses precisely the algebra structure induced by the supplied ring map.
    letI := σ.toAlgebra
    ((ModuleCat.extendScalars σ).obj M) ≃ₗ[S] S ⊗[R] M := by
  -- Local instance justification (defeq pin): match the tensor scalar action declared in the result type.
  letI := σ.toAlgebra
  exact
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The representative line comparison uses the actual exterior scalar map. -/
def extendedLineIso (σ : R →+* S) (P : Model R) :
    -- Local instance justification (defeq pin): determinant scalar extension is formed along this specified ring map.
    letI := σ.toAlgebra
    ModuleCat.of S (S ⊗[R] CochainComplex.Determinant.line P.complex) ≅
      ModuleCat.of S (CochainComplex.Determinant.line (extendedModel σ P).complex) := by
  -- Local instance justification (defeq pin): use the same ring-map-induced tensor action in both determinant endpoint comparisons.
  letI := σ.toAlgebra
  let eNeg := Module.Determinant.mapIso (extendedTermEquiv σ (P.complex.X (-1)))
  let eZero := Module.Determinant.mapIso (extendedTermEquiv σ (P.complex.X 0))
  exact ((DeterminantScalarChange.lineEquiv R S (P.complex.X (-1)) (P.complex.X 0)).trans
    (LinearEquiv.arrowCongr eNeg.symm eZero.symm)).toModuleIso

/-- Canonical determinant scalar extension: exterior base change followed by
the inverse of the specified representative comparison. -/
def baseChangeIso (σ : R →+* S) (K : Object R) :
    (ModuleCat.extendScalars σ).obj ((determinantFunctor R).obj ⟨K⟩).of.obj ≅
      ((determinantFunctor S).obj ⟨extendedObject σ K⟩).of.obj :=
  extendedLineIso σ (model R K) ≪≫
    (representativeIso S (extendedObject σ K)
      (extendedModel σ (model R K)).complex (extendedRealization σ K)).symm

/-- Scalar extension of the prescribed derived isomorphism, retaining both
perfectness and Tor-amplitude subcategory witnesses. -/
def extendedIso (σ : R →+* S) {K L : Object R} (a : K ≅ L) :
    extendedObject σ K ≅ extendedObject σ L :=
  ObjectProperty.isoMk _
    (ObjectProperty.isoMk _ ((ModuleCat.derivedExtensionOfScalars σ).mapIso (underlyingIso R a)))

theorem baseChangeIso_naturality (σ : R →+* S) {K L : Object R} (a : K ≅ L) :
    (ModuleCat.extendScalars σ).map ((determinantFunctor R).map ⟨a⟩).iso.hom.hom ≫
        (baseChangeIso σ L).hom =
      (baseChangeIso σ K).hom ≫
        ((determinantFunctor S).map ⟨extendedIso σ a⟩).iso.hom.hom := by sorry

/-- The genuine base-change comparison preserves the canonical determinant
element under the scalar-extension unit, for rank-zero objects. -/
theorem extendedRankZero (σ : R →+* S) (K : Object R) (hK : isRankZero R K) :
    isRankZero S (extendedObject σ K) := by sorry

theorem baseChangeIso_canonical (σ : R →+* S) (K : Object R) (hK : isRankZero R K) :
    -- Local instance justification (defeq pin): the displayed pure tensor is taken along the ring map in the comparison.
    letI := σ.toAlgebra
    (baseChangeIso σ K).hom ((1 : S) ⊗ₜ[R] canonicalElement R K hK) =
      canonicalElement S (extendedObject σ K) (extendedRankZero σ K hK) := by sorry

end CanonicalRingDeterminant
