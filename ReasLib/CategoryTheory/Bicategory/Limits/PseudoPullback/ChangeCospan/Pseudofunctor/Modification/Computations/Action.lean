/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Pseudofunctor.Modification.Construction.Component

/-!
# Action computations for readable change-of-cospan modifications

This leaf contains component and naturality readouts for the concrete readable
modification action. Strong-transformation field readouts live in
`Computations.StrongTrans`.
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

/-- A readable modification component acts by the identity on the cone apex.
-/
@[simp]
theorem changeCospan.modification.map.apex
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    PseudoPullbackCone.map (changeCospan.modification.map Γ S) =
      𝟙 S.pt := sorry

/-- The comparison of a readable modification component is the identity-cone
comparison followed by the readable cospan modification.
-/
@[simp]
theorem changeCospan.modification.map.fac
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    PseudoPullbackCone.fac (changeCospan.modification.map Γ S) =
      PseudoPullbackCone.fac (𝟙 (S.changeCospan ψ)) ≫
        changeCospan.modification Γ S := sorry

/-- The first-leg comparison of a readable modification component is the identity-cone
comparison followed by the left endpoint component of the cospan modification. -/
@[simp]
theorem changeCospan.modification.map.fstFac
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    PseudoPullbackCone.fstFac (changeCospan.modification.map Γ S) =
      PseudoPullbackCone.fstFac (𝟙 (S.changeCospan ψ)) ≫
        S.fst ◁ CospanTransform.Hom.left Γ := sorry

/-- The second-leg comparison of a readable modification component is the identity-cone
comparison followed by the right endpoint component of the cospan modification. -/
@[simp]
theorem changeCospan.modification.map.sndFac
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    PseudoPullbackCone.sndFac (changeCospan.modification.map Γ S) =
      PseudoPullbackCone.sndFac (𝟙 (S.changeCospan ψ)) ≫
        S.snd ◁ CospanTransform.Hom.right Γ := sorry

/-- The central comparison of a readable modification component is the identity-cone
comparison followed by the conjugated base component of the cospan modification. -/
@[simp]
theorem changeCospan.modification.map.baseFac
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    PseudoPullbackCone.baseFac (changeCospan.modification.map Γ S) =
      PseudoPullbackCone.baseFac (𝟙 (S.changeCospan ψ)) ≫
        (changeCospan.presentation.baseIso S ψ).hom ≫
        (S.fst ≫ f) ◁ CospanTransform.Hom.base Γ ≫
        (changeCospan.presentation.baseIso S φ).inv := sorry

/-- The component induced by an identity cospan modification is the identity
readable cone morphism.
-/
@[simp]
theorem changeCospan.modification.map.id
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    changeCospan.modification.map (𝟙 ψ) S =
      𝟙 (S.changeCospan ψ) := sorry

/-- Readable modification components reverse vertical composition, as required
by the colax orientation of pseudocone morphisms.
-/
@[simp]
theorem changeCospan.modification.map.comp
    {ψ φ χ : CospanTransform f g f' g'}
    (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ)
    (S : PseudoPullbackCone f g) :
    changeCospan.modification.map (Γ ≫ Δ) S =
      changeCospan.modification.map Δ S ≫
        changeCospan.modification.map Γ S := sorry

/-- The forward apex cell of readable modification naturality agrees with the
neutral postcomposition strong transformation.
-/
@[simp]
theorem changeCospan.modification.naturality.hom.apex
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map₂
        (changeCospan.modification.naturality Γ u).hom =
      PseudoCone.map₂
        ((PseudoCone.postcomposeModificationStrongTrans Γ).naturality
          u.hom).hom := sorry

/-- The inverse apex cell of readable modification naturality agrees with the
neutral postcomposition strong transformation.
-/
@[simp]
theorem changeCospan.modification.naturality.inv.apex
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map₂
        (changeCospan.modification.naturality Γ u).inv =
      PseudoCone.map₂
        ((PseudoCone.postcomposeModificationStrongTrans Γ).naturality
          u.hom).inv := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
