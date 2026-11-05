/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PresheafMonoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The symmetric monoidal category of modules on a commutative ringed site

Module sheafification is a localization of the pointwise symmetric monoidal category of module
presheaves.  This file records the compatibility of its weak equivalences with tensor products
and uses Mathlib's monoidal-localization construction to put the canonical symmetric monoidal
structure on module sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

namespace Tensor

section Descent

open Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {O}
variable {P₁ P₂ Q H : PresheafOfModules.{w} (ringSheaf J O).obj}
variable (f : P₁ ⟶ P₂)
variable [PresheafOfModules.IsLocallyInjective J f]
variable [PresheafOfModules.IsLocallySurjective J f]
variable (hH : Presheaf.IsSheaf J H.presheaf) (θ : P₁ ⊗ Q ⟶ H)

private def pairValue (U : Cᵒᵖ) (x : P₁.obj U) (y : Q.obj U) : H.obj U :=
  θ.app U (x ⊗ₜ[O.obj.obj U] y)

private theorem pairValue_natural {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : P₁.obj U) (y : Q.obj U) :
    H.map i (pairValue θ U x y) = pairValue θ V (P₁.map i x) (Q.map i y) := by
  exact (PresheafOfModules.naturality_apply θ i _).symm.trans
    (congrArg (θ.app V) (PresheafOfModules.Monoidal.tensorObj_map_tmul i x y))

private theorem restriction_id (M : PresheafOfModules.{w} (ringSheaf J O).obj)
    (U : Cᵒᵖ) (x : M.obj U) : M.map (𝟙 U) x = x := by
  change M.presheaf.map (𝟙 U) x = x
  rw [M.presheaf.map_id]
  rfl

include hH

private theorem pairValue_eq {U : Cᵒᵖ} (x x' : P₁.obj U) (y : Q.obj U)
    (hx : f.app U x = f.app U x') : pairValue θ U x y = pairValue θ U x' y := by
  apply hH.isSeparated _ _
    (Presheaf.equalizerSieve_mem J ((PresheafOfModules.toPresheaf _).map f) x x' hx)
  intro V a ha
  change H.map a.op (pairValue θ U x y) = H.map a.op (pairValue θ U x' y)
  rw [pairValue_natural, pairValue_natural]
  change P₁.map a.op x = P₁.map a.op x' at ha
  rw [ha]

private def localFamily (U : Cᵒᵖ) (p : P₂.obj U) (q : Q.obj U) :
    Presieve.FamilyOfElements (H.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{w})
      (Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map f) p).arrows :=
  fun V a ha ↦ pairValue θ (op V)
    (Presheaf.localPreimage ((PresheafOfModules.toPresheaf _).map f) p a ha)
    (Q.map a.op q)

private theorem localFamily_compatible (U : Cᵒᵖ) (p : P₂.obj U) (q : Q.obj U) :
    (localFamily f θ U p q).Compatible := by
  intro V₁ V₂ W g₁ g₂ a₁ a₂ ha₁ ha₂ comm
  change H.map g₁.op (pairValue θ _ _ _) = H.map g₂.op (pairValue θ _ _ _)
  rw [pairValue_natural, pairValue_natural]
  have hq : Q.map g₁.op (Q.map a₁.op q) = Q.map g₂.op (Q.map a₂.op q) := by
    rw [← Q.map_comp_apply, ← Q.map_comp_apply, ← op_comp, ← op_comp, comm]
  rw [hq]
  apply pairValue_eq f hH θ
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  change P₂.map g₁.op
      (((PresheafOfModules.toPresheaf _).map f).app _
        (Presheaf.localPreimage ((PresheafOfModules.toPresheaf _).map f) p a₁ ha₁)) =
    P₂.map g₂.op
      (((PresheafOfModules.toPresheaf _).map f).app _
        (Presheaf.localPreimage ((PresheafOfModules.toPresheaf _).map f) p a₂ ha₂))
  rw [Presheaf.app_localPreimage, Presheaf.app_localPreimage]
  change P₂.map g₁.op (P₂.map a₁.op p) = P₂.map g₂.op (P₂.map a₂.op p)
  rw [← P₂.map_comp_apply, ← P₂.map_comp_apply, ← op_comp, ← op_comp, comm]

private def sectionValue (U : Cᵒᵖ) (p : P₂.obj U) (q : Q.obj U) : H.obj U :=
  let htype := (isSheaf_iff_isSheaf_of_type J _).mp
    (Presheaf.isSheaf_comp_of_isSheaf J _ (CategoryTheory.forget AddCommGrpCat.{w}) hH)
  (htype _ (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) p)).amalgamate
    (localFamily f θ U p q) (localFamily_compatible f hH θ U p q)

private theorem sectionValue_restrict (U : Cᵒᵖ) (p : P₂.obj U) (q : Q.obj U)
    {V : C} (a : V ⟶ U.unop) (x : P₁.obj (op V))
    (hx : f.app (op V) x = P₂.map a.op p) :
    H.map a.op (sectionValue f hH θ U p q) = pairValue θ (op V) x (Q.map a.op q) := by
  have ha : Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map f) p a := ⟨x, hx⟩
  let htype := (isSheaf_iff_isSheaf_of_type J _).mp
    (Presheaf.isSheaf_comp_of_isSheaf J _ (CategoryTheory.forget AddCommGrpCat.{w}) hH)
  have hglue := (htype _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) p)).valid_glue
      (localFamily_compatible f hH θ U p q) a ha
  change H.map a.op (sectionValue f hH θ U p q) =
    pairValue θ (op V)
      (Presheaf.localPreimage ((PresheafOfModules.toPresheaf _).map f) p a ha)
      (Q.map a.op q) at hglue
  rw [hglue]
  apply pairValue_eq f hH θ
  exact (Presheaf.app_localPreimage ((PresheafOfModules.toPresheaf _).map f) p a ha).trans hx.symm

private theorem sectionValue_add_left (U : Cᵒᵖ) (p p' : P₂.obj U) (q : Q.obj U) :
    sectionValue f hH θ U (p + p') q =
      sectionValue f hH θ U p q + sectionValue f hH θ U p' q := by
  apply hH.isSeparated _ _ (J.intersection_covering
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) p)
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) p'))
  rintro V a ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩
  change H.map a.op (sectionValue f hH θ U (p + p') q) =
    H.map a.op (sectionValue f hH θ U p q + sectionValue f hH θ U p' q)
  change f.app (op V) x = P₂.map a.op p at hx
  change f.app (op V) x' = P₂.map a.op p' at hx'
  rw [(H.map a.op).hom.map_add,
    sectionValue_restrict f hH θ U p q a x hx,
    sectionValue_restrict f hH θ U p' q a x' hx']
  rw [sectionValue_restrict f hH θ U (p + p') q a (x + x')
    (by rw [(f.app _).hom.map_add, (P₂.map a.op).hom.map_add, hx, hx'])]
  exact (congrArg (θ.app _) (TensorProduct.add_tmul _ _ _)).trans ((θ.app _).hom.map_add _ _)

private theorem sectionValue_smul_left (U : Cᵒᵖ) (r : O.obj.obj U)
    (p : P₂.obj U) (q : Q.obj U) :
    sectionValue f hH θ U (r • p) q = r • sectionValue f hH θ U p q := by
  apply hH.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) p)
  rintro V a ⟨x, hx⟩
  change H.map a.op (sectionValue f hH θ U (r • p) q) =
    H.map a.op (r • sectionValue f hH θ U p q)
  change f.app (op V) x = P₂.map a.op p at hx
  rw [H.map_smul, sectionValue_restrict f hH θ U p q a x hx,
    sectionValue_restrict f hH θ U (r • p) q a
      (O.obj.map a.op r • (show P₁.obj (op V) from x))
      (by rw [(f.app _).hom.map_smul, P₂.map_smul, hx]; rfl)]
  exact (congrArg (θ.app (op V))
    (TensorProduct.smul_tmul' (R := O.obj.obj (op V)) (O.obj.map a.op r)
      (show P₁.obj (op V) from x) (Q.map a.op q)).symm).trans
        ((θ.app (op V)).hom.map_smul _ _)

private theorem sectionValue_add_right (U : Cᵒᵖ) (p : P₂.obj U) (q q' : Q.obj U) :
    sectionValue f hH θ U p (q + q') =
      sectionValue f hH θ U p q + sectionValue f hH θ U p q' := by
  apply hH.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) p)
  rintro V a ⟨x, hx⟩
  change H.map a.op (sectionValue f hH θ U p (q + q')) =
    H.map a.op (sectionValue f hH θ U p q + sectionValue f hH θ U p q')
  change f.app (op V) x = P₂.map a.op p at hx
  rw [(H.map a.op).hom.map_add,
    sectionValue_restrict f hH θ U p (q + q') a x hx,
    sectionValue_restrict f hH θ U p q a x hx,
    sectionValue_restrict f hH θ U p q' a x hx, (Q.map a.op).hom.map_add]
  exact (congrArg (θ.app _) (TensorProduct.tmul_add _ _ _)).trans ((θ.app _).hom.map_add _ _)

private theorem sectionValue_smul_right (U : Cᵒᵖ) (r : O.obj.obj U)
    (p : P₂.obj U) (q : Q.obj U) :
    sectionValue f hH θ U p (r • q) = r • sectionValue f hH θ U p q := by
  apply hH.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) p)
  rintro V a ⟨x, hx⟩
  change H.map a.op (sectionValue f hH θ U p (r • q)) =
    H.map a.op (r • sectionValue f hH θ U p q)
  change f.app (op V) x = P₂.map a.op p at hx
  rw [H.map_smul,
    sectionValue_restrict f hH θ U p (r • q) a x hx,
    sectionValue_restrict f hH θ U p q a x hx, Q.map_smul]
  exact (congrArg (θ.app (op V))
    (TensorProduct.tmul_smul (R := O.obj.obj (op V)) (O.obj.map a.op r)
      (show P₁.obj (op V) from x) (Q.map a.op q))).trans
        ((θ.app (op V)).hom.map_smul _ _)

private theorem sectionValue_natural {U V : Cᵒᵖ} (i : U ⟶ V)
    (p : P₂.obj U) (q : Q.obj U) :
    H.map i (sectionValue f hH θ U p q) =
      sectionValue f hH θ V (P₂.map i p) (Q.map i q) := by
  apply hH.isSeparated _ _ (J.pullback_stable i.unop
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) p))
  rintro W a ⟨x, hx⟩
  change H.map a.op (H.map i (sectionValue f hH θ U p q)) =
    H.map a.op (sectionValue f hH θ V (P₂.map i p) (Q.map i q))
  change f.app (op W) x = P₂.map (a ≫ i.unop).op p at hx
  rw [← H.map_comp_apply]
  change H.map (a ≫ i.unop).op (sectionValue f hH θ U p q) =
    H.map a.op (sectionValue f hH θ V (P₂.map i p) (Q.map i q))
  rw [sectionValue_restrict f hH θ U p q (a ≫ i.unop) x hx,
    sectionValue_restrict f hH θ V (P₂.map i p) (Q.map i q) a x
      (by simpa only [op_comp, Quiver.Hom.op_unop, P₂.map_comp_apply] using hx)]
  rw [op_comp, Quiver.Hom.op_unop, Q.map_comp_apply]

private def descendTensorApp (U : Cᵒᵖ) : (P₂ ⊗ Q).obj U ⟶ H.obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun (p : P₂.obj U) (q : Q.obj U) ↦ sectionValue f hH θ U p q)
    (sectionValue_add_left f hH θ U)
    (sectionValue_smul_left f hH θ U)
    (sectionValue_add_right f hH θ U)
    (sectionValue_smul_right f hH θ U)

private def descendTensor : P₂ ⊗ Q ⟶ H where
  app U := descendTensorApp f hH θ U
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p q
    change descendTensorApp f hH θ V ((P₂ ⊗ Q).map i (p ⊗ₜ[O.obj.obj U] q)) =
      H.map i (descendTensorApp f hH θ U (p ⊗ₜ[O.obj.obj U] q))
    have hmap : (P₂ ⊗ Q).map i (p ⊗ₜ[O.obj.obj U] q) =
        P₂.map i p ⊗ₜ[O.obj.obj V] Q.map i q := rfl
    rw [hmap]
    change sectionValue f hH θ V (P₂.map i p) (Q.map i q) =
      H.map i (sectionValue f hH θ U p q)
    exact (sectionValue_natural f hH θ i p q).symm

private theorem descendTensor_fac : (f ▷ Q) ≫ descendTensor f hH θ = θ := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x q
  change (descendTensor f hH θ).app U (f.app U x ⊗ₜ[O.obj.obj U] q) = pairValue θ U x q
  change sectionValue f hH θ U (f.app U x) q = pairValue θ U x q
  have heval := sectionValue_restrict f hH θ U (f.app U x) q (𝟙 U.unop) x
    (by simp only [op_id, restriction_id])
  simpa only [op_id, restriction_id] using heval

private theorem tensor_precomp_injective :
    Function.Injective (fun ψ : P₂ ⊗ Q ⟶ H ↦ (f ▷ Q) ≫ ψ) := by
  intro ψ ψ' heq
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  change pairValue ψ U p q = pairValue ψ' U p q
  apply hH.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) p)
  rintro V a ⟨x, hx⟩
  change H.map a.op (pairValue ψ U p q) = H.map a.op (pairValue ψ' U p q)
  change f.app (op V) x = P₂.map a.op p at hx
  rw [pairValue_natural, pairValue_natural, ← hx]
  have heval := congrArg (fun η ↦ η.app (op V) (x ⊗ₜ[O.obj.obj (op V)] Q.map a.op q)) heq
  exact heval

private theorem tensor_precomp_bijective :
    Function.Bijective (fun ψ : P₂ ⊗ Q ⟶ H ↦ (f ▷ Q) ≫ ψ) :=
  ⟨tensor_precomp_injective f hH, fun ψ ↦ ⟨descendTensor f hH ψ, descendTensor_fac f hH ψ⟩⟩

end Descent

/-- The morphisms of module presheaves that are locally bijective after forgetting the module
structure. -/
@[stacks 0GMW "weak equivalences for module sheafification"]
abbrev weakEquivalences :
    MorphismProperty (PresheafOfModules.{w} (ringSheaf J O).obj) :=
  J.W.inverseImage (PresheafOfModules.toPresheaf (ringSheaf J O).obj)

private theorem weakEquivalences_whiskerRight
    {P₁ P₂ : PresheafOfModules.{w} (ringSheaf J O).obj}
    (f : P₁ ⟶ P₂) (hf : weakEquivalences O f)
    (Q : PresheafOfModules.{w} (ringSheaf J O).obj) :
    weakEquivalences O (f ▷ Q) := by
  letI : PresheafOfModules.IsLocallyInjective J f := hf.isLocallyInjective
  letI : PresheafOfModules.IsLocallySurjective J f := hf.isLocallySurjective
  rw [weakEquivalences, PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 (ringSheaf J O).obj)]
  change IsIso ((PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).map (f ▷ Q))
  apply isIso_of_coyoneda_map_bijective
  intro N
  rw [(PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).map_comp_bijective_iff]
  exact tensor_precomp_bijective f N.isSheaf

/-- The tensor product of two locally bijective module-presheaf morphisms is locally bijective.
This is the mathematical closure statement needed by monoidal localization; exposing it separately
keeps proofs and downstream uses independent of the packaging as an `IsMonoidal` instance. -/
@[stacks 0GMW "tensor stability of locally bijective module-presheaf morphisms"]
theorem weakEquivalences_tensorHom
    {F₁ F₂ G₁ G₂ : PresheafOfModules.{w} (ringSheaf J O).obj}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂)
    (hf : weakEquivalences O f) (hg : weakEquivalences O g) :
    weakEquivalences O (f ⊗ₘ g) := by
  let a := PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)
  have hright : IsIso (a.map (f ▷ G₁)) := by
    have h := weakEquivalences_whiskerRight O f hf G₁
    rwa [weakEquivalences,
      PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
        (𝟙 (ringSheaf J O).obj)] at h
  have hswap : IsIso (a.map (g ▷ F₂)) := by
    have h := weakEquivalences_whiskerRight O g hg F₂
    rwa [weakEquivalences,
      PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
        (𝟙 (ringSheaf J O).obj)] at h
  have hleft : IsIso (a.map (F₂ ◁ g)) := by
    have hbraid : F₂ ◁ g =
        (β_ F₂ G₁).hom ≫ (g ▷ F₂) ≫ (β_ F₂ G₂).inv := by
      calc
        F₂ ◁ g = (F₂ ◁ g ≫ (β_ F₂ G₂).hom) ≫ (β_ F₂ G₂).inv := by simp
        _ = _ := by rw [BraidedCategory.braiding_naturality_right, Category.assoc]
    rw [hbraid, a.map_comp, a.map_comp]
    infer_instance
  rw [weakEquivalences,
    PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (ringSheaf J O).obj)]
  change IsIso (a.map (f ⊗ₘ g))
  rw [tensorHom_def, a.map_comp]
  infer_instance

/-- Locally bijective module-presheaf morphisms form a monoidal morphism property. -/
@[stacks 0GMW "monoidal weak equivalences for module sheafification"]
instance weakEquivalences.isMonoidal :
    (weakEquivalences O).IsMonoidal :=
  MorphismProperty.IsMonoidal.mk' _ (weakEquivalences_tensorHom O)

/-- The monoidal structure on module sheaves obtained from the monoidal localization of module
presheaves. -/
@[stacks 0GMW "monoidal localization presentation of module sheaves", reducible]
noncomputable def monoidalCategory
    : MonoidalCategory (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  inferInstanceAs <| MonoidalCategory <|
    LocalizedMonoidal
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj))
      (weakEquivalences O) (Iso.refl _)

end Tensor

/-- The canonical monoidal structure on modules over a commutative ring sheaf. -/
@[stacks 0GMW "canonical monoidal structure on module sheaves", reducible]
noncomputable instance moduleMonoidalCategory
    : MonoidalCategory (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  Tensor.monoidalCategory O

namespace Tensor

/-- Module sheafification is monoidal for the canonical localization monoidal structures. -/
@[stacks 0GMW "module sheafification is monoidal"]
noncomputable instance sheafificationMonoidal
    : (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O).obj)).Monoidal :=
  inferInstanceAs <|
    (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj))
      (weakEquivalences O) (Iso.refl _)).Monoidal

/-- The symmetric structure on module sheaves obtained from the symmetric monoidal localization
of module presheaves. -/
@[stacks 0GMW "canonical tensor product on module sheaves", reducible]
noncomputable def symmetricCategory
    : SymmetricCategory (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  inferInstanceAs <| SymmetricCategory <|
    LocalizedMonoidal
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj))
      (weakEquivalences O) (Iso.refl _)

end Tensor

/-- The canonical symmetry on modules over a commutative ring sheaf. -/
@[stacks 0GMW "canonical symmetry on module sheaves", reducible]
noncomputable instance moduleSymmetricCategory
    : SymmetricCategory (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  Tensor.symmetricCategory O

namespace ModuleOver

/-- The canonical monoidal structure on the direct `over` presentation of a restricted module
sheaf category.  This bridge lets typeclass search pass from the underlying ring-sheaf
presentation back to the commutative ring sheaf `O.over U`. -/
@[stacks 0GMW "canonical tensor product on a slice site"]
noncomputable instance monoidalCategory (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    MonoidalCategory (SheafOfModules.{w} ((ringSheaf J O).over U)) :=
  moduleMonoidalCategory (J := J.over U) (O.over U)

/-- The canonical symmetry on the direct `over` presentation of a restricted module sheaf
category. -/
@[stacks 0GMW "canonical symmetry on a slice site"]
noncomputable instance symmetricCategory (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    SymmetricCategory (SheafOfModules.{w} ((ringSheaf J O).over U)) :=
  moduleSymmetricCategory (J := J.over U) (O.over U)

end ModuleOver

end SheafOfModules.RingedSite
