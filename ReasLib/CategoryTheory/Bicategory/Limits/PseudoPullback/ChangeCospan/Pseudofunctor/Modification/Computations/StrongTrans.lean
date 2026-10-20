/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Pseudofunctor.Modification.Construction.StrongTrans

/-!
# Strong-transformation computations for readable change-of-cospan modifications

This leaf records the fields and functoriality formulas of the packaged
`changeCospan.modification.strongTrans`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- The object component of a readable modification strong transformation is
the corresponding contravariant cone morphism.
-/
@[simp]
theorem changeCospan.modification.strongTrans.app
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    (changeCospan.modification.strongTrans Γ).app S =
      changeCospan.modification.map Γ S := sorry

/-- The naturality isomorphism of a readable modification strong
transformation is the explicit readable naturality isomorphism.
-/
@[simp]
theorem changeCospan.modification.strongTrans.naturality
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (changeCospan.modification.strongTrans Γ).naturality u =
      changeCospan.modification.naturality Γ u := sorry

/-- Readable change of cospan sends an identity modification to the identity
strong transformation.
-/
@[simp]
theorem changeCospan.modification.strongTrans.id
    (ψ : CospanTransform f g f' g') :
    changeCospan.modification.strongTrans (𝟙 ψ) =
      Pseudofunctor.StrongTrans.id
        (changeCospan.pseudofunctor ψ) := sorry

/-- The object component of the strong transformation induced by an identity
modification is the identity readable cone morphism.
-/
@[simp]
theorem changeCospan.modification.strongTrans.id.app
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    (changeCospan.modification.strongTrans (𝟙 ψ)).app S =
      𝟙 (S.changeCospan ψ) := sorry

/-- Readable modification strong transformations reverse vertical
composition.
-/
@[simp]
theorem changeCospan.modification.strongTrans.comp
    {ψ φ χ : CospanTransform f g f' g'}
    (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ) :
    changeCospan.modification.strongTrans (Γ ≫ Δ) =
      Pseudofunctor.StrongTrans.vcomp
        (changeCospan.modification.strongTrans Δ)
        (changeCospan.modification.strongTrans Γ) := sorry

/-- Object components display reversed vertical composition as ordinary
composition of readable cone morphisms.
-/
@[simp]
theorem changeCospan.modification.strongTrans.comp.app
    {ψ φ χ : CospanTransform f g f' g'}
    (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ)
    (S : PseudoPullbackCone f g) :
    (changeCospan.modification.strongTrans (Γ ≫ Δ)).app S =
      (changeCospan.modification.strongTrans Δ).app S ≫
        (changeCospan.modification.strongTrans Γ).app S := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
