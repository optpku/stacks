/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Internal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pure tensor sections on a ringed site

The tensor product of module sheaves is a sheafification rather than an objectwise tensor
product.  This file owns the canonical map from two local sections to a local section of the
tensor product, obtained from the sheafification unit and its monoidal comparison.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (𝒪 : Sheaf J CommRingCat.{w})

/-- The pure tensor of two local sections of module sheaves on a commutative ringed site. -/
@[stacks 03L6 "pure tensor of local module-sheaf sections"]
noncomputable def tensorSection
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (U : Cᵒᵖ)
    (x : F.val.obj U) (y : G.val.obj U) :
    (tensorObj F G).val.obj U :=
  (ModuleSheafification.tensorObjIso 𝒪 F G).inv.val.app U
    ((moduleSheafificationUnitToVal 𝒪
      (PresheafOfModules.Monoidal.tensorObj F.val G.val)).app U (x ⊗ₜ y))

/-- Pure tensor sections are additive in the right argument. -/
theorem tensorSection_add_right
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (U : Cᵒᵖ)
    (x : F.val.obj U) (y y' : G.val.obj U) :
    tensorSection 𝒪 U x (y + y') =
      tensorSection 𝒪 U x y + tensorSection 𝒪 U x y' := sorry

/-- Pure tensor sections are linear in the right argument. -/
theorem tensorSection_smul_right
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (U : Cᵒᵖ)
    (x : F.val.obj U) (r : 𝒪.obj.obj U) (y : G.val.obj U) :
    tensorSection 𝒪 U x (r • y) =
      (RingHom.id (𝒪.obj.obj U)) r • tensorSection 𝒪 U x y := sorry

/-- Right-linear pure tensoring by a fixed local section. -/
noncomputable def tensorSectionRight
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (U : Cᵒᵖ) (x : F.val.obj U) :
    G.val.obj U →ₗ[𝒪.obj.obj U] (tensorObj F G).val.obj U where
  toFun := tensorSection 𝒪 U x
  map_add' := tensorSection_add_right 𝒪 U x
  map_smul' := tensorSection_smul_right (F := F) (G := G) 𝒪 U x

/-- Right-linear pure tensoring is additive in its fixed left argument. -/
theorem tensorSectionRight_add
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (U : Cᵒᵖ)
    (x x' : F.val.obj U) :
    tensorSectionRight (G := G) 𝒪 U (x + x') =
      tensorSectionRight (G := G) 𝒪 U x +
        tensorSectionRight (G := G) 𝒪 U x' := sorry

/-- Right-linear pure tensoring is linear in its fixed left argument. -/
theorem tensorSectionRight_smul
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (U : Cᵒᵖ)
    (r : 𝒪.obj.obj U) (x : F.val.obj U) :
    tensorSectionRight (G := G) 𝒪 U (r • x) =
      r • tensorSectionRight (G := G) 𝒪 U x := sorry

/-- The canonical bilinear map from two local section modules to sections of their tensor
product sheaf. -/
@[stacks 03L6 "bilinear pure-tensor map on local sections"]
noncomputable def tensorSectionLinear
    (F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (U : Cᵒᵖ) :
    F.val.obj U →ₗ[𝒪.obj.obj U]
      G.val.obj U →ₗ[𝒪.obj.obj U] (tensorObj F G).val.obj U where
  toFun := tensorSectionRight (G := G) 𝒪 U
  map_add' := tensorSectionRight_add (G := G) 𝒪 U
  map_smul' := tensorSectionRight_smul (G := G) 𝒪 U

/-- The bilinear pure-tensor map evaluates to `tensorSection`. -/
@[simp]
theorem tensorSectionLinear_apply
    (F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (U : Cᵒᵖ)
    (x : F.val.obj U) (y : G.val.obj U) :
    tensorSectionLinear 𝒪 F G U x y = tensorSection 𝒪 U x y := sorry

/-- Pure tensor sections commute with restriction maps. -/
theorem tensorSection_map
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : F.val.obj U) (y : G.val.obj U) :
    ((tensorObj F G).val.map i).hom (tensorSection 𝒪 U x y) =
      tensorSection 𝒪 V ((F.val.map i).hom x) ((G.val.map i).hom y) := sorry

variable [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/-- The morphism of underlying type-valued sheaves sending a pair of sections to their
pure tensor. -/
noncomputable def tensorSectionUnderlying
    (F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J 𝒪)).obj F ⊗
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J 𝒪)).obj G ⟶
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J 𝒪)).obj (tensorObj F G) where
  hom :=
    { app := fun U ↦ TypeCat.ofHom fun p ↦ tensorSection 𝒪 U p.1 p.2
      naturality := by
        intro U V i
        apply ConcreteCategory.hom_ext
        intro p
        exact (tensorSection_map 𝒪 i p.1 p.2).symm }

/-- Pure tensor sections are natural in both module-sheaf arguments. -/
theorem tensorSection_naturality
    {F F' G G' : ringedSiteModuleCategory.{u, v, w, w} J 𝒪}
    (f : F ⟶ F') (g : G ⟶ G') (U : Cᵒᵖ)
    (x : F.val.obj U) (y : G.val.obj U) :
    (((tensorHom f g).val.app U).hom) (tensorSection 𝒪 U x y) =
      tensorSection 𝒪 U (((f.val.app U).hom) x) (((g.val.app U).hom) y) := sorry

/-- The monoidal associator identifies the two iterated pure tensor sections. -/
theorem tensorSection_assoc
    {F G H : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (U : Cᵒᵖ)
    (x : F.val.obj U) (y : G.val.obj U) (z : H.val.obj U) :
    ((((α_ F G H).hom).val.app U).hom)
        (tensorSection 𝒪 U (tensorSection 𝒪 U x y) z) =
      tensorSection 𝒪 U x (tensorSection 𝒪 U y z) := sorry

/-- The symmetric braiding swaps the factors of a pure tensor section. -/
theorem tensorSection_braiding
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (U : Cᵒᵖ)
    (x : F.val.obj U) (y : G.val.obj U) :
    ((((β_ F G).hom).val.app U).hom) (tensorSection 𝒪 U x y) =
      tensorSection 𝒪 U y x := sorry

end SheafOfModules.RingedSite


