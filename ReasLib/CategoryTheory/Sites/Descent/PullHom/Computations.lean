/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.OppositeLocallyDiscrete
public import ReasLib.CategoryTheory.Sites.Descent.PullHom.Basic

/-!
# Composite and comparison computations for `pullHom`

This module records the expanded composite and pseudofunctor-comparison calculations for
`Pseudofunctor.LocallyDiscreteOpToCat.pullHom`.
-/

@[expose] public section

universe u v uX vX

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]

namespace Pseudofunctor.LocallyDiscreteOpToCat

variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX}}

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a triple composite back along a further base morphism is the composite of the three
pulled-back morphisms. -/
theorem pullHom_comp₃
    {X₁ X₂ X₃ X₄ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {M₄ : F.obj (.mk (op X₄))}
    {A₀ : C} {f₁ : A₀ ⟶ X₁} {f₂ : A₀ ⟶ X₂} {f₃ : A₀ ⟶ X₃} {f₄ : A₀ ⟶ X₄}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (χ : (F.map f₃.op.toLoc).toFunctor.obj M₃ ⟶
      (F.map f₄.op.toLoc).toFunctor.obj M₄)
    {A₁ : C} (k : A₁ ⟶ A₀) (kf₁ : A₁ ⟶ X₁) (kf₂ : A₁ ⟶ X₂)
    (kf₃ : A₁ ⟶ X₃) (kf₄ : A₁ ⟶ X₄)
    (hkf₁ : k ≫ f₁ = kf₁) (hkf₂ : k ≫ f₂ = kf₂)
    (hkf₃ : k ≫ f₃ = kf₃) (hkf₄ : k ≫ f₄ = kf₄) :
    pullHom (F := F) (X₁ := X₁) (X₂ := X₄) (M₁ := M₁) (M₂ := M₄)
        (f₁ := f₁) (f₂ := f₄) (Y' := A₁) (φ ≫ ψ ≫ χ) k kf₁ kf₄ hkf₁ hkf₄ =
      pullHom (F := F) (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂)
          (f₁ := f₁) (f₂ := f₂) (Y' := A₁) φ k kf₁ kf₂ hkf₁ hkf₂ ≫
        pullHom (F := F) (X₁ := X₂) (X₂ := X₃) (M₁ := M₂) (M₂ := M₃)
          (f₁ := f₂) (f₂ := f₃) (Y' := A₁) ψ k kf₂ kf₃ hkf₂ hkf₃ ≫
        pullHom (F := F) (X₁ := X₃) (X₂ := X₄) (M₁ := M₃) (M₂ := M₄)
          (f₁ := f₃) (f₂ := f₄) (Y' := A₁) χ k kf₃ kf₄ hkf₃ hkf₄ := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a fourfold composite back along a further base morphism is the composite of the four
pulled-back morphisms. -/
theorem pullHom_comp₄
    {X₁ X₂ X₃ X₄ X₅ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {M₄ : F.obj (.mk (op X₄))} {M₅ : F.obj (.mk (op X₅))}
    {A₀ : C} {f₁ : A₀ ⟶ X₁} {f₂ : A₀ ⟶ X₂} {f₃ : A₀ ⟶ X₃}
    {f₄ : A₀ ⟶ X₄} {f₅ : A₀ ⟶ X₅}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (χ : (F.map f₃.op.toLoc).toFunctor.obj M₃ ⟶
      (F.map f₄.op.toLoc).toFunctor.obj M₄)
    (ω : (F.map f₄.op.toLoc).toFunctor.obj M₄ ⟶
      (F.map f₅.op.toLoc).toFunctor.obj M₅)
    {A₁ : C} (k : A₁ ⟶ A₀) (kf₁ : A₁ ⟶ X₁) (kf₂ : A₁ ⟶ X₂)
    (kf₃ : A₁ ⟶ X₃) (kf₄ : A₁ ⟶ X₄) (kf₅ : A₁ ⟶ X₅)
    (hkf₁ : k ≫ f₁ = kf₁) (hkf₂ : k ≫ f₂ = kf₂)
    (hkf₃ : k ≫ f₃ = kf₃) (hkf₄ : k ≫ f₄ = kf₄)
    (hkf₅ : k ≫ f₅ = kf₅) :
    pullHom (F := F) (X₁ := X₁) (X₂ := X₅) (M₁ := M₁) (M₂ := M₅)
        (f₁ := f₁) (f₂ := f₅) (Y' := A₁) (φ ≫ ψ ≫ χ ≫ ω) k kf₁ kf₅ hkf₁ hkf₅ =
      pullHom (F := F) (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂)
          (f₁ := f₁) (f₂ := f₂) (Y' := A₁) φ k kf₁ kf₂ hkf₁ hkf₂ ≫
        pullHom (F := F) (X₁ := X₂) (X₂ := X₃) (M₁ := M₂) (M₂ := M₃)
          (f₁ := f₂) (f₂ := f₃) (Y' := A₁) ψ k kf₂ kf₃ hkf₂ hkf₃ ≫
        pullHom (F := F) (X₁ := X₃) (X₂ := X₄) (M₁ := M₃) (M₂ := M₄)
          (f₁ := f₃) (f₂ := f₄) (Y' := A₁) χ k kf₃ kf₄ hkf₃ hkf₄ ≫
        pullHom (F := F) (X₁ := X₄) (X₂ := X₅) (M₁ := M₄) (M₂ := M₅)
          (f₁ := f₄) (f₂ := f₅) (Y' := A₁) ω k kf₄ kf₅ hkf₄ hkf₅ := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a fivefold composite back along a further base morphism is the composite of the five
pulled-back morphisms. -/
theorem pullHom_comp₅
    {X₁ X₂ X₃ X₄ X₅ X₆ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {M₄ : F.obj (.mk (op X₄))} {M₅ : F.obj (.mk (op X₅))}
    {M₆ : F.obj (.mk (op X₆))}
    {A₀ : C} {f₁ : A₀ ⟶ X₁} {f₂ : A₀ ⟶ X₂} {f₃ : A₀ ⟶ X₃}
    {f₄ : A₀ ⟶ X₄} {f₅ : A₀ ⟶ X₅} {f₆ : A₀ ⟶ X₆}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (χ : (F.map f₃.op.toLoc).toFunctor.obj M₃ ⟶
      (F.map f₄.op.toLoc).toFunctor.obj M₄)
    (ω : (F.map f₄.op.toLoc).toFunctor.obj M₄ ⟶
      (F.map f₅.op.toLoc).toFunctor.obj M₅)
    (τ : (F.map f₅.op.toLoc).toFunctor.obj M₅ ⟶
      (F.map f₆.op.toLoc).toFunctor.obj M₆)
    {A₁ : C} (k : A₁ ⟶ A₀) (kf₁ : A₁ ⟶ X₁) (kf₂ : A₁ ⟶ X₂)
    (kf₃ : A₁ ⟶ X₃) (kf₄ : A₁ ⟶ X₄) (kf₅ : A₁ ⟶ X₅) (kf₆ : A₁ ⟶ X₆)
    (hkf₁ : k ≫ f₁ = kf₁) (hkf₂ : k ≫ f₂ = kf₂)
    (hkf₃ : k ≫ f₃ = kf₃) (hkf₄ : k ≫ f₄ = kf₄)
    (hkf₅ : k ≫ f₅ = kf₅) (hkf₆ : k ≫ f₆ = kf₆) :
    pullHom (F := F) (X₁ := X₁) (X₂ := X₆) (M₁ := M₁) (M₂ := M₆)
        (f₁ := f₁) (f₂ := f₆) (Y' := A₁) (φ ≫ ψ ≫ χ ≫ ω ≫ τ)
        k kf₁ kf₆ hkf₁ hkf₆ =
      pullHom (F := F) (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂)
          (f₁ := f₁) (f₂ := f₂) (Y' := A₁) φ k kf₁ kf₂ hkf₁ hkf₂ ≫
        pullHom (F := F) (X₁ := X₂) (X₂ := X₃) (M₁ := M₂) (M₂ := M₃)
          (f₁ := f₂) (f₂ := f₃) (Y' := A₁) ψ k kf₂ kf₃ hkf₂ hkf₃ ≫
        pullHom (F := F) (X₁ := X₃) (X₂ := X₄) (M₁ := M₃) (M₂ := M₄)
          (f₁ := f₃) (f₂ := f₄) (Y' := A₁) χ k kf₃ kf₄ hkf₃ hkf₄ ≫
        pullHom (F := F) (X₁ := X₄) (X₂ := X₅) (M₁ := M₄) (M₂ := M₅)
          (f₁ := f₄) (f₂ := f₅) (Y' := A₁) ω k kf₄ kf₅ hkf₄ hkf₅ ≫
        pullHom (F := F) (X₁ := X₅) (X₂ := X₆) (M₁ := M₅) (M₂ := M₆)
          (f₁ := f₅) (f₂ := f₆) (Y' := A₁) τ k kf₅ kf₆ hkf₅ hkf₆ := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back a pseudofunctor composition comparison inverse gives the corresponding
composition comparison inverse on the smaller base. -/
theorem pullHom_mapComp'_inv
    {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (h : X₂ ⟶ X₀) (k : X₃ ⟶ X₂)
    (M : F.obj (.mk (op X₁))) :
    pullHom (F := F)
        ((F.mapCompOp' f h (h ≫ f) rfl).inv.toNatTrans.app M)
        k (k ≫ h) ((k ≫ h) ≫ f) rfl (Category.assoc k h f).symm =
      (F.mapCompOp' f (k ≫ h) ((k ≫ h) ≫ f) rfl).inv.toNatTrans.app M := sorry

set_option backward.isDefEq.respectTransparency false in
/-- The same as `pullHom_mapComp'_inv`, with an explicit factorization equality for the
composite base arrow. -/
theorem pullHom_mapComp'_inv_of_fac
    {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (h : X₂ ⟶ X₀) (k : X₃ ⟶ X₂)
    (kh : X₃ ⟶ X₀) (hkh : k ≫ h = kh)
    (M : F.obj (.mk (op X₁))) :
    pullHom (F := F)
        ((F.mapCompOp' f h (h ≫ f) rfl).inv.toNatTrans.app M)
        k kh (kh ≫ f) hkh
          ((Category.assoc k h f).symm.trans (congrArg (fun l => l ≫ f) hkh)) =
      (F.mapCompOp' f kh (kh ≫ f) rfl).inv.toNatTrans.app M := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back the image under a pseudofunctor restriction functor is just the image under the
composite restriction functor. -/
theorem pullHom_map_of_fac
    {X₀ Y Z : C} (h : Y ⟶ X₀) (k : Z ⟶ Y) (kh : Z ⟶ X₀) (hkh : k ≫ h = kh)
    {M N : F.obj (.mk (op X₀))} (ψ : M ⟶ N) :
    pullHom (F := F) ((F.map h.op.toLoc).toFunctor.map ψ)
      k kh kh hkh hkh =
    (F.map kh.op.toLoc).toFunctor.map ψ := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Literal-composite form of `pullHom_map_of_fac`.

Restricting the image of a fiber morphism along `k` is its image under the
composite restriction along `k ≫ h`. -/
theorem pullHom_map_comp
    {X₀ Y Z : C} (h : Y ⟶ X₀) (k : Z ⟶ Y)
    {M N : F.obj (.mk (op X₀))} (ψ : M ⟶ N) :
    pullHom (F := F) ((F.map h.op.toLoc).toFunctor.map ψ)
      k (k ≫ h) (k ≫ h) =
    (F.map (k ≫ h).op.toLoc).toFunctor.map ψ := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back a pseudofunctor composition comparison gives the corresponding comparison on the
smaller base. -/
theorem pullHom_mapComp'_hom
    {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (h : X₂ ⟶ X₀) (k : X₃ ⟶ X₂)
    (M : F.obj (.mk (op X₁))) :
    pullHom (F := F)
        ((F.mapCompOp' f h (h ≫ f) rfl).hom.toNatTrans.app M)
        k ((k ≫ h) ≫ f) (k ≫ h) (Category.assoc k h f).symm rfl =
      (F.mapCompOp' f (k ≫ h) ((k ≫ h) ≫ f) rfl).hom.toNatTrans.app M := sorry

set_option backward.isDefEq.respectTransparency false in
/-- The same as `pullHom_mapComp'_hom`, with an explicit factorization equality for the
composite base arrow. -/
theorem pullHom_mapComp'_hom_of_fac
    {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (h : X₂ ⟶ X₀) (k : X₃ ⟶ X₂)
    (kh : X₃ ⟶ X₀) (hkh : k ≫ h = kh)
    (M : F.obj (.mk (op X₁))) :
    pullHom (F := F)
        ((F.mapCompOp' f h (h ≫ f) rfl).hom.toNatTrans.app M)
        k (kh ≫ f) kh
        ((Category.assoc k h f).symm.trans (congrArg (fun l => l ≫ f) hkh)) hkh =
      (F.mapCompOp' f kh (kh ≫ f) rfl).hom.toNatTrans.app M := sorry

end Pseudofunctor.LocallyDiscreteOpToCat

end CategoryTheory
