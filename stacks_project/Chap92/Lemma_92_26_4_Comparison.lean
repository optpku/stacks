/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap92.Lemma_92_26_2_Comparison

/-!
# Cotangent complex of an algebraic space over a ring

For a ring `Λ` and an algebraic space `X` over `Spec Λ`, this module owns the
constant sheaf `underline{Λ}` on `X_étale`, the algebra map `underline{Λ} ⟶ 𝒪_X`,
the sheaf-level cotangent `L_{𝒪_X / underline{Λ}}`, and the canonical identification
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

variable {S : Scheme.{u}}

/-- The constant sheaf on a small étale site with value the universe lift of a commutative ring. -/
def constRingSheafOf (X : AlgebraicSpace S) (R : CommRingCat.{u}) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  (constantSheaf (smallEtaleTopology X) CommRingCat.{u + 1}).obj
    (CommRingCat.universeLift.{u, u + 1}.obj R)

/-- `constRingSheafOf` is the constant sheaf on the universe lift of `R`. -/
theorem constRingSheafOf_eq (X : AlgebraicSpace S) (R : CommRingCat.{u}) :
    constRingSheafOf X R =
      (constantSheaf (smallEtaleTopology X) CommRingCat.{u + 1}).obj
        (CommRingCat.universeLift.{u, u + 1}.obj R) :=
  rfl

/-- Weak sheafification of commutative ring sheaves on the small étale site. -/
instance hasWeakSheafify_commRing (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) CommRingCat.{u} :=
  sorry

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

/-- The structure morphism `X ⟶ S` of an algebraic space over `S`. -/
def toSpecSpace (X : AlgebraicSpace S) : X ⟶ ofOver (Over.mk (𝟙 S)) :=
  toBase X

/-- `toSpecSpace` is `toBase`. -/
theorem toSpecSpace_eq (X : AlgebraicSpace S) : toSpecSpace X = toBase X :=
  rfl

/-- Component of the constant-to-structure map on `Spec Λ` at an étale object. -/
def constToStructureOnSpecPresheafApp (Λ : CommRingCat.{u})
    (U : (smallEtaleSite (specAsSpace Λ))ᵒᵖ) :
    ((Functor.const (smallEtaleSite (specAsSpace Λ))ᵒᵖ).obj Λ).obj U ⟶
      (commStructureSheaf (specAsSpace Λ)).obj.obj U :=
  (Scheme.ΓSpecIso Λ).inv ≫ ((smallEtaleToOver (specAsSpace Λ)).obj U.unop).hom.appTop

/-- Unfolding of `constToStructureOnSpecPresheafApp`. -/
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
  commSheafInverseImageObj (toSpecSpace X) (constRingSheafOnSpec Λ)

/-- `constRingSheafUnlifted` is the inverse image of `constRingSheafOnSpec`. -/
theorem constRingSheafUnlifted_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constRingSheafUnlifted Λ X =
      commSheafInverseImageObj (toSpecSpace X) (constRingSheafOnSpec Λ) :=
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
    constRingSheafUnlifted Λ X ⟶ commInverseImageStructureSheaf (toSpecSpace X) :=
  commSheafInverseImageMap (toSpecSpace X) (constToStructureOnSpec Λ)

/-- `constToInverseImageUnlifted` is the inverse image of `constToStructureOnSpec`. -/
theorem constToInverseImageUnlifted_eq (Λ : CommRingCat.{u})
    (X : AlgebraicSpace (Spec Λ)) :
    constToInverseImageUnlifted Λ X =
      commSheafInverseImageMap (toSpecSpace X) (constToStructureOnSpec Λ) :=
  rfl

/-- Component of the constant-to-structure presheaf map at an étale object. -/
def constToStructurePresheafApp (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))
    (U : (smallEtaleSite X)ᵒᵖ) :
    ((Functor.const (smallEtaleSite X)ᵒᵖ).obj
        (CommRingCat.universeLift.{u, u + 1}.obj Λ)).obj U ⟶
      (commStructureSheafLift X).obj.obj U :=
  (CommRingCat.universeLift.{u, u + 1}).map
    ((Scheme.ΓSpecIso Λ).inv ≫ ((smallEtaleToOver X).obj U.unop).hom.appTop)

/-- Unfolding of `constToStructurePresheafApp`. -/
theorem constToStructurePresheafApp_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))
    (U : (smallEtaleSite X)ᵒᵖ) :
    constToStructurePresheafApp Λ X U =
      (CommRingCat.universeLift.{u, u + 1}).map
        ((Scheme.ΓSpecIso Λ).inv ≫ ((smallEtaleToOver X).obj U.unop).hom.appTop) :=
  rfl

/-- The constant-to-structure map of presheaves, before sheafification. -/
def constToStructurePresheaf (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    (Functor.const (smallEtaleSite X)ᵒᵖ).obj
        (CommRingCat.universeLift.{u, u + 1}.obj Λ) ⟶
      (commStructureSheafLift X).obj where
  app := constToStructurePresheafApp Λ X
  naturality _ _ _ := sorry

/-- Components of `constToStructurePresheaf` are `constToStructurePresheafApp`. -/
theorem constToStructurePresheaf_app (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))
    (U : (smallEtaleSite X)ᵒᵖ) :
    (constToStructurePresheaf Λ X).app U = constToStructurePresheafApp Λ X U :=
  rfl

/-- Canonical comparison `underline{Λ} ⟶ p⁻¹ 𝒪_{Spec Λ}` on `X_étale`. -/
def constToInverseImage (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constRingSheaf Λ X ⟶ inverseImageLift (toSpecSpace X) :=
  liftSheafMap X (constToInverseImageUnlifted Λ X)

/-- `constToInverseImage` is the universe lift of `constToInverseImageUnlifted`. -/
theorem constToInverseImage_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constToInverseImage Λ X = liftSheafMap X (constToInverseImageUnlifted Λ X) :=
  rfl

/-- The canonical algebra map `underline{Λ} ⟶ 𝒪_X` on `X_étale`. -/
def constToStructure (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constRingSheaf Λ X ⟶ commStructureSheafLift X :=
  constToInverseImage Λ X ≫ structureMapLift (toSpecSpace X)

/-- `constToStructure` is the composite of `constToInverseImage` with the structure map. -/
theorem constToStructure_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constToStructure Λ X =
      constToInverseImage Λ X ≫ structureMapLift (toSpecSpace X) :=
  rfl

/-- Components of `constToStructure` are those of `constToInverseImage` followed by
`structureMapLift`. -/
theorem constToStructure_app (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))
    (U : (smallEtaleSite X)ᵒᵖ) :
    (constToStructure Λ X).hom.app U =
      (constToInverseImage Λ X).hom.app U ≫
        (structureMapLift (toSpecSpace X)).hom.app U :=
  sorry

/-- The sheaf-level cotangent complex `L_{𝒪_X / underline{Λ}}`. -/
def constCotangentCochain (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    CochainComplex (CommModules X) ℤ :=
  cotangentCochainObj (constToStructure Λ X)

/-- Unfolding of `constCotangentCochain`. -/
theorem constCotangentCochain_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constCotangentCochain Λ X = cotangentCochainObj (constToStructure Λ X) :=
  rfl

/-- The object `L_{𝒪_X / underline{Λ}}` in `D(𝒪_X)`. -/
def constCotangent (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    DerivedCategory (CommModules X) :=
  DerivedCategory.Q.obj (constCotangentCochain Λ X)

/-- Unfolding of `constCotangent`. -/
theorem constCotangent_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constCotangent Λ X = DerivedCategory.Q.obj (constCotangentCochain Λ X) :=
  rfl

/-- The triangle `constToInverseImage ≫ structureMapLift (toSpecSpace X) = constToStructure`
commutes. -/
theorem constToInverseImage_comp (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constToInverseImage Λ X ≫ structureMapLift (toSpecSpace X) =
      constToStructure Λ X ≫ 𝟙 (commStructureSheafLift X) :=
  sorry

/-- Degreewise map of simplicial cotangent modules induced by `constToInverseImage`. -/
def spaceOverRingCompareSimplicial (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule (constRingSheaf Λ X) (Under.mk (constToStructure Λ X))).obj n ⟶
      (simplicialModule (inverseImageLift (toSpecSpace X))
        (Under.mk (structureMapLift (toSpecSpace X)))).obj n :=
  baseChangeSimplicialHom (constToInverseImage Λ X) (constToStructure Λ X)
    (structureMapLift (toSpecSpace X)) (constToInverseImage_comp Λ X) n

/-- The cochain map `L_{𝒪_X / underline{Λ}} ⟶ L_{X / Spec Λ}` induced by the algebra
triangle of `constToInverseImage`. -/
def spaceOverRingCompareCochain (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constCotangentCochain Λ X ⟶ cotangentCochain (toSpecSpace X) where
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
                (simplicialModule (inverseImageLift (toSpecSpace X))
                  (Under.mk (structureMapLift (toSpecSpace X)))))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).inv
    | none => 0
  comm' := sorry

/-- Unfolding of `spaceOverRingCompareCochain` in cohomological degree `-n`. -/
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
              (simplicialModule (inverseImageLift (toSpecSpace X))
                (Under.mk (structureMapLift (toSpecSpace X)))))
            embeddingDownNat rfl).inv :=
  sorry

/-- The canonical comparison `L_{𝒪_X / underline{Λ}} ⟶ L_{X / Spec Λ}` in `D(𝒪_X)`. -/
def spaceOverRingCompare (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    constCotangent Λ X ⟶ cotangent (toSpecSpace X) :=
  DerivedCategory.Q.map (spaceOverRingCompareCochain Λ X)

/-- Unfolding of `spaceOverRingCompare`. -/
theorem spaceOverRingCompare_eq (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    spaceOverRingCompare Λ X = DerivedCategory.Q.map (spaceOverRingCompareCochain Λ X) :=
  rfl

/-- The comparison `L_{𝒪_X / underline{Λ}} ⟶ L_{X / Spec Λ}` is an isomorphism in `D(𝒪_X)`. -/
instance spaceOverRingCompare_isIso (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    IsIso (spaceOverRingCompare Λ X) :=
  sorry

/-- The canonical identification `L_{X / Spec Λ} ≅ L_{𝒪_X / underline{Λ}}` in `D(𝒪_X)`. -/
def spaceOverRingIso (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    cotangent (toSpecSpace X) ≅ constCotangent Λ X :=
  (asIso (spaceOverRingCompare Λ X)).symm

/-- The forward map of `spaceOverRingIso` is the inverse of `spaceOverRingCompare`. -/
theorem spaceOverRingIso_hom (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    (spaceOverRingIso Λ X).hom = CategoryTheory.inv (spaceOverRingCompare Λ X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
