/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.EtaleLocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.CommRing

/-!
# Cotangent complex of an algebraic space over a ring

For a ring `Λ` and an algebraic space `X` over `Spec Λ`, the
constant sheaf `underline{Λ}` on `X_étale` has an algebra map `underline{Λ} ⟶ 𝒪_X`,
giving the sheaf-level cotangent `L_{𝒪_X / underline{Λ}}` and its canonical identification
with `L_{X / Spec Λ}` in `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open HomologicalComplex
open ComplexShape
open Opposite
open AlgebraicTopology
open SheafOfModules.RingedSite
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

/-- `Spec Λ` as an algebraic space over itself. -/
abbrev specAsSpace (Λ : CommRingCat.{u}) : AlgebraicSpace (Spec Λ) :=
  ofOver (Over.mk (𝟙 (Spec Λ)))

/-- `specAsSpace Λ` is `Spec Λ` viewed as an algebraic space over itself. -/
theorem specAsSpace_eq (Λ : CommRingCat.{u}) :
    specAsSpace Λ = ofOver (Over.mk (𝟙 (Spec Λ))) :=
  rfl

/-- The constant sheaf `underline{Λ}` on the small étale site of `Spec Λ`. -/
def constRingSheafOnSpec (Λ : CommRingCat.{u}) :
    Sheaf (smallEtaleTopology (specAsSpace Λ)) CommRingCat.{u} :=
  (constantSheaf (smallEtaleTopology (specAsSpace Λ)) CommRingCat.{u}).obj Λ

/-- `constRingSheafOnSpec` is the constant sheaf with value `Λ`. -/
theorem constRingSheafOnSpec_eq (Λ : CommRingCat.{u}) :
    constRingSheafOnSpec Λ =
      (constantSheaf (smallEtaleTopology (specAsSpace Λ)) CommRingCat.{u}).obj Λ :=
  rfl

/-- Component of the constant-to-structure map on `Spec Λ` at an étale object. -/
def constToStructureOnSpecPresheafApp (Λ : CommRingCat.{u})
    (U : (smallEtaleSite (specAsSpace Λ))ᵒᵖ) :
    ((Functor.const (smallEtaleSite (specAsSpace Λ))ᵒᵖ).obj Λ).obj U ⟶
      (commStructureSheaf (specAsSpace Λ)).obj.obj U :=
  (Scheme.ΓSpecIso Λ).inv ≫ ((smallEtaleToOver (specAsSpace Λ)).obj U.unop).hom.appTop

/-- The coefficient map on an étale object over the affine base is pullback of global sections after the affine-spectrum identification. -/
theorem constToStructureOnSpecPresheafApp_eq (Λ : CommRingCat.{u})
    (U : (smallEtaleSite (specAsSpace Λ))ᵒᵖ) :
    constToStructureOnSpecPresheafApp Λ U =
      (Scheme.ΓSpecIso Λ).inv ≫
        ((smallEtaleToOver (specAsSpace Λ)).obj U.unop).hom.appTop :=
  rfl

/-- The constant-to-structure map of presheaves on `Spec Λ`, before sheafification. -/
def constToStructureOnSpecPresheaf (Λ : CommRingCat.{u}) :
    (Functor.const (smallEtaleSite (specAsSpace Λ))ᵒᵖ).obj Λ ⟶
      (commStructureSheaf (specAsSpace Λ)).obj where
  app := constToStructureOnSpecPresheafApp Λ
  naturality _ _ _ := sorry

/-- Components of `constToStructureOnSpecPresheaf` are `constToStructureOnSpecPresheafApp`. -/
theorem constToStructureOnSpecPresheaf_app (Λ : CommRingCat.{u})
    (U : (smallEtaleSite (specAsSpace Λ))ᵒᵖ) :
    (constToStructureOnSpecPresheaf Λ).app U =
      constToStructureOnSpecPresheafApp Λ U :=
  rfl

/-- The canonical algebra map `underline{Λ} ⟶ 𝒪_{Spec Λ}` on `(Spec Λ)_étale`. -/
def constToStructureOnSpec (Λ : CommRingCat.{u}) :
    constRingSheafOnSpec Λ ⟶ commStructureSheaf (specAsSpace Λ) :=
  ((sheafificationAdjunction (smallEtaleTopology (specAsSpace Λ)) CommRingCat.{u}).homEquiv
      ((Functor.const _).obj Λ) (commStructureSheaf (specAsSpace Λ))).symm
    (constToStructureOnSpecPresheaf Λ)

/-- `constToStructureOnSpec` is the sheafification adjunct of
`constToStructureOnSpecPresheaf`. -/
theorem constToStructureOnSpec_eq (Λ : CommRingCat.{u}) :
    constToStructureOnSpec Λ =
      ((sheafificationAdjunction (smallEtaleTopology (specAsSpace Λ)) CommRingCat.{u}).homEquiv
          ((Functor.const _).obj Λ) (commStructureSheaf (specAsSpace Λ))).symm
        (constToStructureOnSpecPresheaf Λ) :=
  rfl

/-- Inverse image of the constant sheaf `underline{Λ}` along `X ⟶ Spec Λ`. -/
def constRingSheafUnlifted (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  commSheafInverseImageObj (SchemeRealization.toBase X) (constRingSheafOnSpec Λ)

/-- `constRingSheafUnlifted` is the inverse image of `constRingSheafOnSpec`. -/
theorem constRingSheafUnlifted_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constRingSheafUnlifted Λ X =
      commSheafInverseImageObj (SchemeRealization.toBase X) (constRingSheafOnSpec Λ) :=
  rfl

/-- The constant sheaf `underline{Λ}` on the small étale site of an algebraic space over `Λ`. -/
def constRingSheaf (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  liftSheafObj X (constRingSheafUnlifted Λ X)

/-- `constRingSheaf` is the universe lift of the inverse image of `constRingSheafOnSpec`. -/
theorem constRingSheaf_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constRingSheaf Λ X = liftSheafObj X (constRingSheafUnlifted Λ X) :=
  rfl

/-- Canonical comparison `underline{Λ} ⟶ p⁻¹ 𝒪_{Spec Λ}` on `X_étale`, before universe lift. -/
def constToInverseImageUnlifted (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constRingSheafUnlifted Λ X ⟶ commInverseImageStructureSheaf (SchemeRealization.toBase X) :=
  commSheafInverseImageMap (SchemeRealization.toBase X) (constToStructureOnSpec Λ)

/-- `constToInverseImageUnlifted` is the inverse image of `constToStructureOnSpec`. -/
theorem constToInverseImageUnlifted_eq (Λ : CommRingCat.{u})
    (X : AlgebraicSpace (Spec Λ)) :
    constToInverseImageUnlifted Λ X =
      commSheafInverseImageMap (SchemeRealization.toBase X) (constToStructureOnSpec Λ) :=
  rfl

/-- Canonical comparison `underline{Λ} ⟶ p⁻¹ 𝒪_{Spec Λ}` on `X_étale`. -/
def constToInverseImage (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constRingSheaf Λ X ⟶ inverseImageLift (SchemeRealization.toBase X) :=
  liftSheafMap X (constToInverseImageUnlifted Λ X)

/-- `constToInverseImage` is the universe lift of `constToInverseImageUnlifted`. -/
theorem constToInverseImage_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constToInverseImage Λ X = liftSheafMap X (constToInverseImageUnlifted Λ X) :=
  rfl

/-- The canonical algebra map `underline{Λ} ⟶ 𝒪_X` on `X_étale`. -/
def constToStructure (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constRingSheaf Λ X ⟶ commStructureSheafLift X :=
  constToInverseImage Λ X ≫ structureMapLift (SchemeRealization.toBase X)

/-- `constToStructure` is the composite of `constToInverseImage` with the structure map. -/
theorem constToStructure_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constToStructure Λ X =
      constToInverseImage Λ X ≫ structureMapLift (SchemeRealization.toBase X) :=
  rfl

/-- Components of `constToStructure` are those of `constToInverseImage` followed by
`structureMapLift`. -/
theorem constToStructure_app (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))
    (U : (smallEtaleSite X)ᵒᵖ) :
    (constToStructure Λ X).hom.app U =
      (constToInverseImage Λ X).hom.app U ≫
        (structureMapLift (SchemeRealization.toBase X)).hom.app U :=
  sorry

/-- The sheaf-level cotangent complex `L_{𝒪_X / underline{Λ}}`. -/
def constCotangentCochain (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    CochainComplex (CommModules X) ℤ :=
  cotangentCochainObj (constToStructure Λ X)

/-- The constant-coefficient cotangent cochain complex is formed from the canonical algebra map to the structure sheaf. -/
theorem constCotangentCochain_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constCotangentCochain Λ X = cotangentCochainObj (constToStructure Λ X) :=
  rfl

/-- The object `L_{𝒪_X / underline{Λ}}` in `D(𝒪_X)`. -/
def constCotangent (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    DerivedCategory (CommModules X) :=
  DerivedCategory.Q.obj (constCotangentCochain Λ X)

/-- The constant-coefficient derived cotangent object is the localization of its cochain complex. -/
theorem constCotangent_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constCotangent Λ X = DerivedCategory.Q.obj (constCotangentCochain Λ X) :=
  rfl

/-- The triangle `constToInverseImage ≫ structureMapLift (SchemeRealization.toBase X) = constToStructure`
commutes. -/
theorem constToInverseImage_comp (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constToInverseImage Λ X ≫ structureMapLift (SchemeRealization.toBase X) =
      constToStructure Λ X ≫ 𝟙 (commStructureSheafLift X) :=
  sorry

/-- Degreewise map of simplicial cotangent modules induced by `constToInverseImage`. -/
def spaceOverRingCompareSimplicial (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule (constRingSheaf Λ X) (Under.mk (constToStructure Λ X))).obj n ⟶
      (simplicialModule (inverseImageLift (SchemeRealization.toBase X))
        (Under.mk (structureMapLift (SchemeRealization.toBase X)))).obj n :=
  baseChangeSimplicialHom (constToInverseImage Λ X) (constToStructure Λ X)
    (structureMapLift (SchemeRealization.toBase X)) (constToInverseImage_comp Λ X) n

/-- The cochain map `L_{𝒪_X / underline{Λ}} ⟶ L_{X / Spec Λ}` induced by the algebra
triangle of `constToInverseImage`. -/
def spaceOverRingCompareCochain (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constCotangentCochain Λ X ⟶ cotangentCochain (SchemeRealization.toBase X) where
  f i :=
    match h : embeddingDownNat.r i with
    | some n =>
        (extendXIso
            ((alternatingFaceMapComplex
                (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift X)))).obj
              (simplicialModule (constRingSheaf Λ X) (Under.mk (constToStructure Λ X))))
            embeddingDownNat
            (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).hom ≫
          spaceOverRingCompareSimplicial Λ X (op ⦋n⦌) ≫
          (extendXIso
              ((alternatingFaceMapComplex
                  (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift X)))).obj
                (simplicialModule (inverseImageLift (SchemeRealization.toBase X))
                  (Under.mk (structureMapLift (SchemeRealization.toBase X)))))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).inv
    | none => 0
  comm' := sorry

/-- In nonpositive cohomological degrees, the comparison is the simplicial change-of-base map transported through the extension identifications. -/
theorem spaceOverRingCompareCochain_f (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))
    (n : ℕ) :
    (spaceOverRingCompareCochain Λ X).f (-n) =
      (extendXIso
          ((alternatingFaceMapComplex
              (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift X)))).obj
            (simplicialModule (constRingSheaf Λ X) (Under.mk (constToStructure Λ X))))
          embeddingDownNat rfl).hom ≫
        spaceOverRingCompareSimplicial Λ X (op ⦋n⦌) ≫
        (extendXIso
            ((alternatingFaceMapComplex
                (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift X)))).obj
              (simplicialModule (inverseImageLift (SchemeRealization.toBase X))
                (Under.mk (structureMapLift (SchemeRealization.toBase X)))))
            embeddingDownNat rfl).inv :=
  sorry

/-- The canonical comparison `L_{𝒪_X / underline{Λ}} ⟶ L_{X / Spec Λ}` in `D(𝒪_X)`. -/
def spaceOverRingCompare (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constCotangent Λ X ⟶ cotangent (SchemeRealization.toBase X) :=
  DerivedCategory.Q.map (spaceOverRingCompareCochain Λ X)

/-- The derived comparison is the localization of the canonical comparison cochain map. -/
theorem spaceOverRingCompare_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    spaceOverRingCompare Λ X = DerivedCategory.Q.map (spaceOverRingCompareCochain Λ X) :=
  rfl

/-- The comparison `L_{𝒪_X / underline{Λ}} ⟶ L_{X / Spec Λ}` is an isomorphism in `D(𝒪_X)`. -/
instance spaceOverRingCompare_isIso (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    IsIso (spaceOverRingCompare Λ X) :=
  sorry

/-- The canonical identification `L_{X / Spec Λ} ≅ L_{𝒪_X / underline{Λ}}` in `D(𝒪_X)`. -/
def spaceOverRingIso (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    cotangent (SchemeRealization.toBase X) ≅ constCotangent Λ X :=
  (asIso (spaceOverRingCompare Λ X)).symm

/-- The forward map of `spaceOverRingIso` is the inverse of `spaceOverRingCompare`. -/
theorem spaceOverRingIso_hom (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    (spaceOverRingIso Λ X).hom = CategoryTheory.inv (spaceOverRingCompare Λ X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
