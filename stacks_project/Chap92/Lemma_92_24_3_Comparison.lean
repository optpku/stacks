/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import stacks_project.Chap92.Definition_92_24_1_Morphism
public import stacks_project.Chap92.Lemma_92_18_8_Triangle

/-!
# Cotangent complex of a scheme over a ring

For a ring `Λ` and a scheme `X` over `Spec Λ`, this module owns the constant sheaf
`underline{Λ}` on the Zariski site of `X`, the algebra map `underline{Λ} ⟶ 𝒪_X`,
the sheaf-level cotangent `L_{𝒪_X / underline{Λ}}`, and the canonical identification
with `L_{X / Spec Λ}` in `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.RingedSpace.Hom
open HomologicalComplex
open ComplexShape
open Opposite
open AlgebraicTopology
open TopCat.Sheaf
open TopologicalSpace
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Cotangent

/-- The constant sheaf `underline{Λ}` on the Zariski opens of a scheme. -/
def constRingSheaf (Λ : CommRingCat.{u}) (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u} :=
  (constantSheaf (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u}).obj Λ

/-- `constRingSheaf` is the constant sheaf with value `Λ`. -/
theorem constRingSheaf_eq (Λ : CommRingCat.{u}) (X : Scheme.{u}) :
    constRingSheaf Λ X =
      (constantSheaf (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u}).obj Λ :=
  sorry

/-- Inverse image `p⁻¹ 𝒪_{Spec Λ}` along the structure morphism `X ↘ Spec Λ`. -/
def inverseImageRingSheaf (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    Sheaf (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u} :=
  (pullback CommRingCat.{u} (X ↘ Spec Λ).toShHom.hom.base).obj (Spec Λ).sheaf

/-- Unfolding of `inverseImageRingSheaf` as pullback of the structure sheaf of `Spec Λ`. -/
theorem inverseImageRingSheaf_eq (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    inverseImageRingSheaf Λ X =
      (pullback CommRingCat.{u} (X ↘ Spec Λ).toShHom.hom.base).obj (Spec Λ).sheaf :=
  sorry

/-- Component of the constant-to-inverse-image presheaf map at an open `U`. -/
def constToInverseImagePresheafApp (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (U : (TopologicalSpace.Opens X.toTopCat)ᵒᵖ) :
    ((Functor.const (TopologicalSpace.Opens X.toTopCat)ᵒᵖ).obj Λ).obj U ⟶
      (inverseImageRingSheaf Λ X).obj.obj U :=
  (Scheme.ΓSpecIso Λ).inv ≫
    (((pullbackPushforwardAdjunction CommRingCat.{u}
            (X ↘ Spec Λ).toShHom.hom.base).unit.app (Spec Λ).sheaf).hom.app (op ⊤) ≫
      (inverseImageRingSheaf Λ X).obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op)

/-- Unfolding of `constToInverseImagePresheafApp`. -/
theorem constToInverseImagePresheafApp_eq (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (U : (TopologicalSpace.Opens X.toTopCat)ᵒᵖ) :
    constToInverseImagePresheafApp Λ X U =
      (Scheme.ΓSpecIso Λ).inv ≫
        (((pullbackPushforwardAdjunction CommRingCat.{u}
                (X ↘ Spec Λ).toShHom.hom.base).unit.app (Spec Λ).sheaf).hom.app (op ⊤) ≫
          (inverseImageRingSheaf Λ X).obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op) :=
  sorry

/-- The constant-to-inverse-image map of presheaves, before sheafification. -/
def constToInverseImagePresheaf (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    (Functor.const (TopologicalSpace.Opens X.toTopCat)ᵒᵖ).obj Λ ⟶ (inverseImageRingSheaf Λ X).obj where
  app := constToInverseImagePresheafApp Λ X
  naturality _ _ _ := sorry

/-- Components of `constToInverseImagePresheaf` are `constToInverseImagePresheafApp`. -/
theorem constToInverseImagePresheaf_app (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (U : (TopologicalSpace.Opens X.toTopCat)ᵒᵖ) :
    (constToInverseImagePresheaf Λ X).app U = constToInverseImagePresheafApp Λ X U :=
  sorry

/-- Canonical comparison `underline{Λ} ⟶ p⁻¹ 𝒪_{Spec Λ}` on the Zariski site of `X`. -/
def constToInverseImage (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    constRingSheaf Λ X ⟶ inverseImageRingSheaf Λ X :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u}).homEquiv
      ((Functor.const _).obj Λ) (inverseImageRingSheaf Λ X)).symm
    (constToInverseImagePresheaf Λ X)

/-- `constToInverseImage` is the sheafification adjunct of `constToInverseImagePresheaf`. -/
theorem constToInverseImage_eq (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    constToInverseImage Λ X =
      ((sheafificationAdjunction (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u}).homEquiv
          ((Functor.const _).obj Λ) (inverseImageRingSheaf Λ X)).symm
        (constToInverseImagePresheaf Λ X) :=
  sorry

/-- The canonical algebra map `underline{Λ} ⟶ 𝒪_X`, as the composite of
`constToInverseImage` with `p♯`. -/
def constToStructure (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    constRingSheaf Λ X ⟶ X.sheaf :=
  constToInverseImage Λ X ≫ inverseImageStructureSheafHomComm (X ↘ Spec Λ).toShHom

/-- Unfolding of `constToStructure` through the inverse-image structure map. -/
theorem constToStructure_eq (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    constToStructure Λ X =
      constToInverseImage Λ X ≫
        inverseImageStructureSheafHomComm (X ↘ Spec Λ).toShHom :=
  sorry

/-- Component of the constant-to-structure map at an open, after the sheafification unit,
via the structure morphism on global sections. -/
def constToStructurePresheafApp (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (U : (TopologicalSpace.Opens X.toTopCat)ᵒᵖ) :
    ((Functor.const (TopologicalSpace.Opens X.toTopCat)ᵒᵖ).obj Λ).obj U ⟶ X.sheaf.obj.obj U :=
  (Scheme.ΓSpecIso Λ).inv ≫
    (X ↘ Spec Λ).appTop ≫ X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op

/-- Unfolding of `constToStructurePresheafApp`. -/
theorem constToStructurePresheafApp_eq (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (U : (TopologicalSpace.Opens X.toTopCat)ᵒᵖ) :
    constToStructurePresheafApp Λ X U =
      (Scheme.ΓSpecIso Λ).inv ≫
        (X ↘ Spec Λ).appTop ≫ X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op :=
  sorry

/-- After the sheafification unit, the component of `constToStructure` at `U` is
`constToStructurePresheafApp`. -/
theorem constToStructure_app (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : (TopologicalSpace.Opens X.toTopCat)ᵒᵖ) :
    ((sheafificationAdjunction (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u}).unit.app
          ((Functor.const _).obj Λ)).app U ≫
        (constToStructure Λ X).hom.app U =
      constToStructurePresheafApp Λ X U :=
  sorry

/-- The triangle `constToInverseImage ≫ p♯ = constToStructure` commutes. -/
theorem constToInverseImage_comp (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    constToInverseImage Λ X ≫ inverseImageStructureSheafHomComm (X ↘ Spec Λ).toShHom =
      constToStructure Λ X ≫ 𝟙 X.sheaf :=
  sorry

/-- The sheaf-level cotangent complex `L_{𝒪_X / underline{Λ}}`. -/
def constCotangentCochain (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    CochainComplex X.Modules ℤ :=
  CotangentComplex.obj (constRingSheaf Λ X) (Under.mk (constToStructure Λ X))

/-- Unfolding of `constCotangentCochain`. -/
theorem constCotangentCochain_eq (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    constCotangentCochain Λ X =
      CotangentComplex.obj (constRingSheaf Λ X) (Under.mk (constToStructure Λ X)) :=
  sorry

/-- The object `L_{𝒪_X / underline{Λ}}` in `D(𝒪_X)`. -/
def constCotangent (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    DerivedCategory X.Modules :=
  DerivedCategory.Q.obj (constCotangentCochain Λ X)

/-- Unfolding of `constCotangent`. -/
theorem constCotangent_eq (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    constCotangent Λ X = DerivedCategory.Q.obj (constCotangentCochain Λ X) :=
  sorry

/-- The cochain map `L_{𝒪_X / underline{Λ}} ⟶ L_{X / Spec Λ}` induced by the algebra
triangle of `constToInverseImage`. -/
def overRingCompareCochain (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    constCotangentCochain Λ X ⟶ Hom.cotangentComplex (X ↘ Spec Λ) :=
  toRelativeMapCochain (constToInverseImage Λ X)
    (inverseImageStructureSheafHomComm (X ↘ Spec Λ).toShHom)

/-- Unfolding of `overRingCompareCochain` as the sheaf-level second transitivity map. -/
theorem overRingCompareCochain_eq (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    overRingCompareCochain Λ X =
      toRelativeMapCochain (constToInverseImage Λ X)
        (inverseImageStructureSheafHomComm (X ↘ Spec Λ).toShHom) :=
  sorry

/-- Unfolding of `overRingCompareCochain` in cohomological degree `-n`. -/
theorem overRingCompareCochain_f (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : ℕ) :
    (overRingCompareCochain Λ X).f (-n) =
      (toRelativeMapCochain (constToInverseImage Λ X)
          (inverseImageStructureSheafHomComm (X ↘ Spec Λ).toShHom)).f (-n) :=
  sorry

/-- The canonical comparison `L_{𝒪_X / underline{Λ}} ⟶ L_{X / Spec Λ}` in `D(𝒪_X)`. -/
def overRingCompare (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    constCotangent Λ X ⟶ DerivedCategory.Q.obj (Hom.cotangentComplex (X ↘ Spec Λ)) :=
  DerivedCategory.Q.map (overRingCompareCochain Λ X)

/-- Unfolding of `overRingCompare`. -/
theorem overRingCompare_eq (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    overRingCompare Λ X = DerivedCategory.Q.map (overRingCompareCochain Λ X) :=
  sorry

/-- The comparison `L_{𝒪_X / underline{Λ}} ⟶ L_{X / Spec Λ}` is an isomorphism in `D(𝒪_X)`. -/
instance overRingCompare_isIso (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    IsIso (overRingCompare Λ X) :=
  sorry

/-- The canonical identification `L_{X / Spec Λ} ≅ L_{𝒪_X / underline{Λ}}` in `D(𝒪_X)`. -/
def overRingIso (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    DerivedCategory.Q.obj (Hom.cotangentComplex (X ↘ Spec Λ)) ≅ constCotangent Λ X :=
  (asIso (overRingCompare Λ X)).symm

/-- The forward map of `overRingIso` is the inverse of `overRingCompare`. -/
theorem overRingIso_hom (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    (overRingIso Λ X).hom = CategoryTheory.inv (overRingCompare Λ X) :=
  sorry

end AlgebraicGeometry.Scheme.Cotangent
