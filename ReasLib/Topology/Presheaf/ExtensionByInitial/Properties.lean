/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Presheaf.ExtensionByInitial.Functor

/-!
# Properties of presheaf extension by an initial object

This module owns the adjunction and full-faithfulness API for extension by an initial object
along an open-subspace inclusion. The underlying construction is owned by
`TopCat.Presheaf.ExtensionByInitial`.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open TopCat.Opens.Subspace

noncomputable section

universe w u

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{w} C] [HasInitial C] [HasColimits C]

namespace TopCat.Presheaf.ExtensionByInitial.Properties

/-- The component on an open of the unit for extension by an initial object. -/
noncomputable def unitApp (U : Opens X) (ℱ : (space U).Presheaf C)
    (V : (Opens (space U))ᵒᵖ) :
    ℱ.obj V ⟶
      ((TopCat.Presheaf.pullback C (inclusion U)).obj
        ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ)).obj V :=
  let hImage : (subspaceInclusionFunctor U).obj (unop V) ≤ U :=
    (U.isOpenEmbedding.functor.map (homOfLE le_top)).le.trans_eq
      (Opens.isOpenEmbedding_obj_top U)
  let hObj :=
    (TopCat.Presheaf.ExtensionByInitial.presheaf_obj_eq_of_le U ℱ hImage).trans
      (congrArg ℱ.obj (congrArg op (Opens.map_functor_eq (unop V))))
  eqToHom hObj.symm ≫
    (U.isOpenEmbedding.isOpenMap.pullbackObjIso
      ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ)).inv.app V

/-- The components of the extension-by-initial unit are natural in the subspace open. -/
theorem unitApp_naturality (U : Opens X) (ℱ : (space U).Presheaf C)
    {V W : (Opens (space U))ᵒᵖ} (i : V ⟶ W) :
    ℱ.map i ≫ unitApp U ℱ W =
      unitApp U ℱ V ≫
        ((TopCat.Presheaf.pullback C (inclusion U)).obj
          ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ)).map i := sorry

/-- The unit natural transformation for extension by an initial object on presheaves. -/
noncomputable def unit (U : Opens X) (ℱ : (space U).Presheaf C) :
    ℱ ⟶ (TopCat.Presheaf.pullback C (inclusion U)).obj
      ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ) where
  app := unitApp U ℱ
  naturality := fun _ _ i => unitApp_naturality U ℱ i

/-- The component on an open of the inverse of the extension-by-initial unit: the pullback of
`jₚ! ℱ` to `U` is computed on the image open, where `jₚ! ℱ` recovers the sections of `ℱ`. -/
noncomputable def unitInvApp (U : Opens X) (ℱ : (space U).Presheaf C)
    (V : (Opens (space U))ᵒᵖ) :
    ((TopCat.Presheaf.pullback C (inclusion U)).obj
        ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ)).obj V ⟶ ℱ.obj V :=
  let hImage : (subspaceInclusionFunctor U).obj (unop V) ≤ U :=
    (U.isOpenEmbedding.functor.map (homOfLE le_top)).le.trans_eq
      (Opens.isOpenEmbedding_obj_top U)
  let hObj :=
    (TopCat.Presheaf.ExtensionByInitial.presheaf_obj_eq_of_le U ℱ hImage).trans
      (congrArg ℱ.obj (congrArg op (Opens.map_functor_eq (unop V))))
  (U.isOpenEmbedding.isOpenMap.pullbackObjIso
      ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ)).hom.app V ≫
    eqToHom hObj

/-- The inverse unit components are natural in the subspace open. -/
theorem unitInvApp_naturality (U : Opens X) (ℱ : (space U).Presheaf C)
    {V W : (Opens (space U))ᵒᵖ} (i : V ⟶ W) :
    ((TopCat.Presheaf.pullback C (inclusion U)).obj
        ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ)).map i ≫ unitInvApp U ℱ W =
      unitInvApp U ℱ V ≫ ℱ.map i := sorry

/-- The explicit inverse of the extension-by-initial unit. -/
noncomputable def unitInv (U : Opens X) (ℱ : (space U).Presheaf C) :
    (TopCat.Presheaf.pullback C (inclusion U)).obj
      ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ) ⟶ ℱ where
  app := unitInvApp U ℱ
  naturality := fun _ _ i ↦ unitInvApp_naturality U ℱ i

/-- The unit followed by its explicit inverse is the identity. -/
theorem unit_comp_unitInv (U : Opens X) (ℱ : (space U).Presheaf C) :
    unit U ℱ ≫ unitInv U ℱ = 𝟙 ℱ := sorry

/-- The explicit inverse followed by the unit is the identity. -/
theorem unitInv_comp_unit (U : Opens X) (ℱ : (space U).Presheaf C) :
    unitInv U ℱ ≫ unit U ℱ = 𝟙 _ := sorry

/-- The extension-by-initial unit `ℱ ≅ j⁻¹ jₚ! ℱ` as an isomorphism with explicit inverse. -/
noncomputable def unitIso (U : Opens X) (ℱ : (space U).Presheaf C) :
    ℱ ≅ (TopCat.Presheaf.pullback C (inclusion U)).obj
      ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ) where
  hom := unit U ℱ
  inv := unitInv U ℱ
  hom_inv_id := unit_comp_unitInv U ℱ
  inv_hom_id := unitInv_comp_unit U ℱ

/-- Transpose a morphism out of extension by initial to a morphism into presheaf pullback. -/
noncomputable def toPullback (U : Opens X) {ℱ : (space U).Presheaf C}
    {𝒢 : X.Presheaf C}
    (η : (TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ ⟶ 𝒢) :
    ℱ ⟶ (TopCat.Presheaf.pullback C (inclusion U)).obj 𝒢 :=
  unit U ℱ ≫ (TopCat.Presheaf.pullback C (inclusion U)).map η

open Classical in
/-- The component on an ambient open of the inverse adjoint transpose. -/
noncomputable def liftApp (U : Opens X) {ℱ : (space U).Presheaf C}
    {𝒢 : X.Presheaf C}
    (η : ℱ ⟶ (TopCat.Presheaf.pullback C (inclusion U)).obj 𝒢)
    (V : (Opens X)ᵒᵖ) :
    ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ).obj V ⟶ 𝒢.obj V :=
  if hV : unop V ≤ U then
    let hImage :
        (subspaceInclusionFunctor U).obj (preimageOpen U (unop V)) = unop V :=
      (Opens.functor_map_eq_inf U (unop V)).trans (inf_eq_left.mpr hV)
    eqToHom
        (TopCat.Presheaf.ExtensionByInitial.presheaf_obj_eq_of_le U ℱ hV) ≫
      η.app (op (preimageOpen U (unop V))) ≫
        (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒢).hom.app
          (op (preimageOpen U (unop V))) ≫
          𝒢.map (eqToHom (congrArg op hImage))
  else
    eqToHom
        (TopCat.Presheaf.ExtensionByInitial.presheaf_obj_eq_of_not_le U ℱ hV) ≫
      initial.to (𝒢.obj V)

/-- The components of the inverse transpose are natural in the ambient open. -/
theorem liftApp_naturality (U : Opens X) {ℱ : (space U).Presheaf C}
    {𝒢 : X.Presheaf C}
    (η : ℱ ⟶ (TopCat.Presheaf.pullback C (inclusion U)).obj 𝒢)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ).map i ≫
        liftApp U η W =
      liftApp U η V ≫ 𝒢.map i := sorry

/-- The inverse adjoint transpose of a morphism into the pullback of a presheaf. -/
noncomputable def lift (U : Opens X) {ℱ : (space U).Presheaf C}
    {𝒢 : X.Presheaf C}
    (η : ℱ ⟶ (TopCat.Presheaf.pullback C (inclusion U)).obj 𝒢) :
    (TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ ⟶ 𝒢 where
  app := liftApp U η
  naturality := fun _ _ i => liftApp_naturality U η i

/-- Inverting the transpose of a morphism out of extension by initial recovers that morphism. -/
theorem lift_toPullback (U : Opens X) {ℱ : (space U).Presheaf C}
    {𝒢 : X.Presheaf C}
    (η : (TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ ⟶ 𝒢) :
    lift U (toPullback U η) = η := sorry

/-- Transposing `lift U η` back along the unit recovers `η`. -/
theorem unit_comp_lift (U : Opens X) {ℱ : (space U).Presheaf C}
    {𝒢 : X.Presheaf C}
    (η : ℱ ⟶ (TopCat.Presheaf.pullback C (inclusion U)).obj 𝒢) :
    unit U ℱ ≫
      (TopCat.Presheaf.pullback C (inclusion U)).map (lift U η) = η := sorry

/-- The Hom equivalence characterizing presheaf extension by an initial object. -/
noncomputable def homEquiv (U : Opens X) (ℱ : (space U).Presheaf C)
    (𝒢 : X.Presheaf C) :
    ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ ⟶ 𝒢) ≃
      (ℱ ⟶ (TopCat.Presheaf.pullback C (inclusion U)).obj 𝒢) where
  toFun := toPullback U
  invFun := lift U
  left_inv := lift_toPullback U
  right_inv := unit_comp_lift U

/-- The inverse transpose is natural in its source presheaf. -/
theorem lift_naturality_left (U : Opens X)
    {ℱ' ℱ : (space U).Presheaf C} {𝒢 : X.Presheaf C}
    (f : ℱ' ⟶ ℱ)
    (g : ℱ ⟶ (TopCat.Presheaf.pullback C (inclusion U)).obj 𝒢) :
    lift U (f ≫ g) =
      (TopCat.Presheaf.ExtensionByInitial.functor U).map f ≫ lift U g := sorry

/-- The forward transpose is natural in its target presheaf. -/
theorem toPullback_naturality_right (U : Opens X)
    {ℱ : (space U).Presheaf C} {𝒢 𝒢' : X.Presheaf C}
    (f : (TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ ⟶ 𝒢)
    (g : 𝒢 ⟶ 𝒢') :
    toPullback U (f ≫ g) =
      toPullback U f ≫ (TopCat.Presheaf.pullback C (inclusion U)).map g := sorry

/-- The adjunction from presheaf extension by an initial object to presheaf pullback. -/
noncomputable def adjunction (U : Opens X) :
    TopCat.Presheaf.ExtensionByInitial.functor U ⊣
      (TopCat.Presheaf.pullback C (inclusion U) :
        X.Presheaf C ⥤ (space U).Presheaf C) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv U
      homEquiv_naturality_left_symm := lift_naturality_left U
      homEquiv_naturality_right := toPullback_naturality_right U }

/-- The extension-by-initial unit is natural in the presheaf. -/
theorem unit_naturality (U : Opens X) {ℱ 𝒢 : (space U).Presheaf C}
    (η : ℱ ⟶ 𝒢) :
    η ≫ unit U 𝒢 =
      unit U ℱ ≫
        (TopCat.Presheaf.pullback C (inclusion U)).map
          ((TopCat.Presheaf.ExtensionByInitial.functor U).map η) := sorry

/-- The explicit unit natural transformation for extension by an initial object. -/
noncomputable def unitNat (U : Opens X) :
    𝟭 ((space U).Presheaf C) ⟶
      TopCat.Presheaf.ExtensionByInitial.functor U ⋙
        TopCat.Presheaf.pullback C (inclusion U) where
  app := unit U
  naturality := fun _ _ η => unit_naturality U η

/-- The component of `unitNat U` is the explicit extension-by-initial unit component. -/
theorem unitNat_app (U : Opens X) (ℱ : (space U).Presheaf C) :
    (unitNat U).app ℱ = unit U ℱ := sorry

/-- The unit of the canonical adjunction is the explicit extension-by-initial unit. -/
theorem adjunction_unit (U : Opens X) :
    (adjunction (C := C) U).unit = unitNat U := sorry

/-- The component of the canonical adjunction unit is the explicit unit component. -/
theorem adjunction_unit_app (U : Opens X) (ℱ : (space U).Presheaf C) :
    (adjunction (C := C) U).unit.app ℱ = unit U ℱ := sorry

/-- The Hom equivalence of the canonical adjunction is the explicit transpose equivalence. -/
theorem adjunction_homEquiv (U : Opens X) (ℱ : (space U).Presheaf C)
    (𝒢 : X.Presheaf C) :
    (adjunction (C := C) U).homEquiv ℱ 𝒢 = homEquiv U ℱ 𝒢 := sorry

/-- The counit component of the canonical adjunction is the inverse transpose of the identity. -/
theorem adjunction_counit_app (U : Opens X) (𝒢 : X.Presheaf C) :
    (adjunction (C := C) U).counit.app 𝒢 =
      lift U (𝟙 ((TopCat.Presheaf.pullback C (inclusion U)).obj 𝒢)) := sorry

/-- The unit of any adjunction with this extension-by-initial functor is an isomorphism. -/
theorem unit_isIso_of_adj (U : Opens X)
    (adj : TopCat.Presheaf.ExtensionByInitial.functor U ⊣
      TopCat.Presheaf.pullback C (inclusion U)) :
    IsIso adj.unit := sorry

/-- The unit of the canonical presheaf extension-by-initial adjunction is an isomorphism. -/
instance unit_isIso (U : Opens X) :
    IsIso (adjunction (C := C) U).unit := by
  rw [adjunction_unit]
  have (ℱ : (space U).Presheaf C) : IsIso ((unitNat (C := C) U).app ℱ) :=
    (unitIso U ℱ).isIso_hom
  exact NatIso.isIso_of_isIso_app _

/-- Presheaf extension by an initial object is fully faithful; a morphism
`jₚ! ℱ ⟶ jₚ! 𝒢` is pulled back along the open inclusion and composed with the explicit inverse
unit. -/
noncomputable def fullyFaithful (U : Opens X) :
    (TopCat.Presheaf.ExtensionByInitial.functor (C := C) U).FullyFaithful where
  preimage {_ 𝒢} f := toPullback U f ≫ unitInv U 𝒢
  map_preimage := sorry
  preimage_map := sorry

/-- The preimage of a morphism is restriction followed by the explicit inverse unit. -/
@[simp] theorem fullyFaithful_preimage (U : Opens X) {ℱ 𝒢 : (space U).Presheaf C}
    (f : (TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ ⟶
      (TopCat.Presheaf.ExtensionByInitial.functor U).obj 𝒢) :
    (fullyFaithful U).preimage f = toPullback U f ≫ unitInv U 𝒢 := rfl

end TopCat.Presheaf.ExtensionByInitial.Properties

end

end
