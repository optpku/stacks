/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Basic computations for canonical Hom-presheaves

This module records the slice-level calculations for the canonical Hom-presheaf
of a `Cat`-valued pseudofunctor on an opposite locally discrete base. Endpoint
actions and strong-transformation functoriality are deliberately kept in
separate modules.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity-slice equivalence from fiber morphisms to the canonical Hom-presheaf commutes
with conjugation by endpoint isomorphisms. -/
@[stacks 026A "Hom-presheaf endpoint conjugation"]
theorem PresheafHom.ObjHomEquiv.homCongr
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (φ : x₁ ⟶ y₁) :
    Iso.homCongr
        ((F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.mapIso ex)
        ((F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.mapIso ey)
        (F.presheafHomObjHomEquiv φ) =
      F.presheafHomObjHomEquiv (ex.inv ≫ φ ≫ ey.hom) := sorry

/-- The identity-slice Hom equivalence is the action of the pseudofunctor on the identity base
morphism. -/
@[stacks 026A "identity-slice Hom-presheaf evaluation"]
theorem PresheafHom.ObjHomEquiv.eqMapId
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y : F.obj (.mk (op U))} (φ : x ⟶ y) :
    F.presheafHomObjHomEquiv φ =
      (F.map (𝟙 U).op.toLoc).toFunctor.map φ := sorry

/-- Restricting an identity-slice Hom section along a base morphism is the pseudofunctorial
image of the represented morphism. This form retains the literal composite `g ≫ 𝟙 W` appearing
in the source slice object. -/
@[stacks 026A "identity-slice Hom-presheaf restriction"]
theorem PresheafHom.Map.IdentitySlice.compId
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {W Z : C} (g : Z ⟶ W)
    (x y : F.obj (.mk (op W))) (φ : x ⟶ y) :
    (F.presheafHom x y).map
        (Over.homMk g : Over.mk (g ≫ 𝟙 W) ⟶ Over.mk (𝟙 W)).op
        (F.presheafHomObjHomEquiv φ) =
      (F.map (g ≫ 𝟙 W).op.toLoc).toFunctor.map φ := sorry

/-- Restricting an identity-slice Hom section, with the source slice object normalized to
`Over.mk g`. -/
@[stacks 026A "normalized Hom-presheaf restriction"]
theorem PresheafHom.Map.IdentitySlice.overMk
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {W Z : C} (g : Z ⟶ W)
    (x y : F.obj (.mk (op W))) (φ : x ⟶ y) :
    (F.presheafHom x y).map
        (Over.homMk g (Category.comp_id g) :
          Over.mk g ⟶ Over.mk (𝟙 W)).op
        (F.presheafHomObjHomEquiv φ) =
      (F.map g.op.toLoc).toFunctor.map φ := sorry

/-- Restriction in a canonical Hom-presheaf preserves isomorphisms. -/
@[stacks 026A "Hom-presheaf restriction preserves isomorphisms"]
theorem PresheafHom.Map.isIso
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} (x y : F.obj (.mk (op U)))
    {W₁ W₂ : (Over U)ᵒᵖ} (α : W₁ ⟶ W₂)
    (φ : (F.presheafHom x y).obj W₁) (hφ : IsIso φ) :
    IsIso ((F.presheafHom x y).map α φ) := sorry

/-- A sheaf canonical Hom-presheaf is separated on every base cover: two fiber morphisms are
equal when all of their reindexings along a cover agree. -/
@[stacks 026A "Hom-presheaf cover extensionality"]
theorem PresheafHom.homExtOfCover
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {W : C} (S : J.Cover W)
    (x y : F.obj (.mk (op W)))
    (hSheaf : Presheaf.IsSheaf (J.over W) (F.presheafHom x y))
    {φ ψ : x ⟶ y}
    (h : ∀ I : S.Arrow,
      (F.map I.f.op.toLoc).toFunctor.map φ =
        (F.map I.f.op.toLoc).toFunctor.map ψ) :
    φ = ψ := sorry

/- The base Hom-presheaf constructor is imported from Mathlib; expose it from the same shared leaf
as the computation lemmas without introducing a redundant alias. -/

end Pseudofunctor

end CategoryTheory
