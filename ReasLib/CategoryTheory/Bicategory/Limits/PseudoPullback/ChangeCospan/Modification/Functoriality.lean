/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Modification.Construction

/-!
# Functoriality of modifications acting on readable changed-cospan cones

This leaf contains exactly the identity and vertical-composition laws required to package
`changeCospan.modification` as an ordinary functor. Component formulas remain independently
available from `Modification.Computations`.
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

/-- Change of cospan sends an identity cospan modification to the identity modification
of the readable transported cone transformation. -/
@[simp]
theorem changeCospan.modification.id
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    changeCospan.modification (𝟙 ψ) S =
      𝟙 (S.changeCospan ψ).toPseudoCone.π := sorry

/-- Change of cospan preserves vertical composition of modifications between parallel
cospan transformations. -/
@[simp]
theorem changeCospan.modification.comp
    {ψ φ χ : CospanTransform f g f' g'}
    (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ)
    (S : PseudoPullbackCone f g) :
    changeCospan.modification (Γ ≫ Δ) S =
      changeCospan.modification Γ S ≫
        changeCospan.modification Δ S := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
