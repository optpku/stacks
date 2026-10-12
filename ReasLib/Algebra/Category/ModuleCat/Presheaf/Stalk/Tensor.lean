/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products and stalks of module presheaves

This file constructs the canonical tensor-stalk comparison for module presheaves directly from
the filtered-colimit presentation of a stalk.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace

noncomputable section

universe u

namespace PresheafOfModules.Tensor.Stalk

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
variable (F G : PresheafOfModules
  (CategoryTheory.Presheaf.ringPresheafOfComm R)) (x : X)

/-- The stalk of the pointwise tensor product of two module presheaves. -/
abbrev source : ModuleCat (R.stalk x) :=
  PresheafOfModules.stalkModuleCatOfCommRing
    (PresheafOfModules.Monoidal.tensorObj F G) x

/-- The tensor product over the stalk ring of the two module-presheaf stalks. -/
abbrev target : ModuleCat (R.stalk x) :=
  PresheafOfModules.stalkModuleCatOfCommRing F x ⊗
    PresheafOfModules.stalkModuleCatOfCommRing G x

/-- The pure tensor of the germs of two sections over a common neighborhood. -/
def germTensor (U : Opens X) (hx : x ∈ U)
    (m : F.obj (op U)) (n : G.obj (op U)) : target F G x :=
  TopCat.Presheaf.germ F.presheaf U x hx m ⊗ₜ[R.stalk x]
    TopCat.Presheaf.germ G.presheaf U x hx n

/-- Taking a germ tensor preserves addition in the first variable. -/
theorem germTensor_add_left (U : Opens X) (hx : x ∈ U)
    (m m' : F.obj (op U)) (n : G.obj (op U)) :
    germTensor F G x U hx (m + m') n =
      germTensor F G x U hx m n + germTensor F G x U hx m' n := sorry

/-- Taking a germ tensor is semilinear in the first variable over the germ map. -/
theorem germTensor_smul_left (U : Opens X) (hx : x ∈ U)
    (r : R.obj (op U)) (m : F.obj (op U)) (n : G.obj (op U)) :
    germTensor F G x U hx (r • m) n =
      R.germ U x hx r • germTensor F G x U hx m n := sorry

/-- Taking a germ tensor preserves addition in the second variable. -/
theorem germTensor_add_right (U : Opens X) (hx : x ∈ U)
    (m : F.obj (op U)) (n n' : G.obj (op U)) :
    germTensor F G x U hx m (n + n') =
      germTensor F G x U hx m n + germTensor F G x U hx m n' := sorry

/-- Taking a germ tensor is semilinear in the second variable over the germ map. -/
theorem germTensor_smul_right (U : Opens X) (hx : x ∈ U)
    (r : R.obj (op U)) (m : F.obj (op U)) (n : G.obj (op U)) :
    germTensor F G x U hx m (r • n) =
      R.germ U x hx r • germTensor F G x U hx m n := sorry

/-- The map from a neighborhood's pointwise tensor product to the tensor product of the two
stalk modules. -/
noncomputable def leg (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.Monoidal.tensorObj F G).presheaf).obj U) ⟶
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F G x) :=
  AddCommGrpCat.ofHom
    (show
      (PresheafOfModules.Monoidal.tensorObj F G).obj (op U.unop.1) ⟶
        (ModuleCat.restrictScalars (R.germ U.unop.1 x U.unop.2).hom).obj
          (target F G x)
      from ModuleCat.MonoidalCategory.tensorLift
        (germTensor F G x U.unop.1 U.unop.2)
        (germTensor_add_left F G x U.unop.1 U.unop.2)
        (germTensor_smul_left F G x U.unop.1 U.unop.2)
        (germTensor_add_right F G x U.unop.1 U.unop.2)
        (germTensor_smul_right F G x U.unop.1 U.unop.2)).hom.toAddMonoidHom

/-- A neighborhood leg sends a pure tensor to the pure tensor of its two germs. -/
theorem leg_tmul (U : (OpenNhds x)ᵒᵖ)
    (m : F.obj ((OpenNhds.inclusion x).op.obj U))
    (n : G.obj ((OpenNhds.inclusion x).op.obj U)) :
    leg F G x U (m ⊗ₜ n) =
      germTensor F G x U.unop.1 U.unop.2 m n := sorry

/-- The neighborhood tensor maps are compatible with restriction. -/
theorem leg_naturality {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙
        (PresheafOfModules.Monoidal.tensorObj F G).presheaf).map i) ≫
        leg F G x V =
      leg F G x U := sorry

/-- The cocone of neighborhood tensor products with vertex the tensor product of stalks. -/
noncomputable def cocone :
    Cocone ((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.Monoidal.tensorObj F G).presheaf) where
  pt := (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F G x)
  ι :=
    { app := leg F G x
      naturality := fun _ _ i ↦ leg_naturality F G x i }

/-- The additive map from the stalk of the pointwise tensor presheaf to the tensor product of
the two stalk modules. -/
noncomputable def addMap :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.Monoidal.tensorObj F G).presheaf x ⟶
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F G x) :=
  colimit.desc _ (cocone F G x)

/-- The additive tensor-stalk map preserves addition. -/
theorem addMap_add (m n : source F G x) :
    addMap F G x (m + n) = addMap F G x m + addMap F G x n := sorry

/-- The additive tensor-stalk map is linear over the stalk ring. -/
theorem addMap_smul (r : R.stalk x) (m : source F G x) :
    addMap F G x (r • m) =
      HSMul.hSMul (α := R.stalk x) (β := target F G x) r (addMap F G x m) := sorry

/-- The canonical comparison from the stalk of a pointwise tensor product to the tensor product
of the two module-presheaf stalks. -/
@[stacks 01CB "module-presheaf tensor product stalk comparison"]
noncomputable def comparison : source F G x ⟶ target F G x :=
  ModuleCat.ofHom
    { toFun := addMap F G x
      map_add' := addMap_add F G x
      map_smul' := addMap_smul F G x }

/-- The presheaf tensor-stalk comparison sends the germ of a pure tensor to the pure tensor of
the corresponding germs. -/
@[stacks 01CB "module-presheaf tensor product stalk comparison on pure tensors"]
theorem comparison_germ_tmul (U : Opens X) (hx : x ∈ U)
    (m : F.obj (op U)) (n : G.obj (op U)) :
    comparison F G x
        (TopCat.Presheaf.germ
          (PresheafOfModules.Monoidal.tensorObj F G).presheaf U x hx
          (m ⊗ₜ[R.obj (op U)] n)) =
      germTensor F G x U hx m n := sorry

/-- A neighborhood section presenting an element of a module-presheaf stalk. -/
structure Representative
    (H : PresheafOfModules (ringPresheaf R))
    (x : X) where
  /-- The neighborhood on which the representative is defined. -/
  neighborhood : Opens X
  /-- The base point belongs to the representative neighborhood. -/
  memNeighborhood : x ∈ neighborhood
  /-- The section whose germ represents the stalk element. -/
  value : H.obj (op neighborhood)

/-- A chosen neighborhood representative of a module-presheaf stalk element. Its mathematical
content is exposed by `representative_germ`; downstream constructions should use that theorem. -/
noncomputable def representative
    (H : PresheafOfModules (ringPresheaf R))
    (m : PresheafOfModules.stalkModuleCatOfCommRing H x) : Representative H x :=
  let h := TopCat.Presheaf.exists_germ_eq H.presheaf m
  { neighborhood := h.choose
    memNeighborhood := h.choose_spec.choose
    value := h.choose_spec.choose_spec.choose }

/-- The germ of the chosen representative is the original stalk element. -/
theorem representative_germ
    (H : PresheafOfModules (ringPresheaf R))
    (m : PresheafOfModules.stalkModuleCatOfCommRing H x) :
    TopCat.Presheaf.germ H.presheaf (representative x H m).neighborhood x
      (representative x H m).memNeighborhood (representative x H m).value = m := sorry

/-- The common neighborhood used to tensor two chosen stalk representatives. -/
noncomputable def commonOpen
    (m : PresheafOfModules.stalkModuleCatOfCommRing F x)
    (n : PresheafOfModules.stalkModuleCatOfCommRing G x) : Opens X :=
  (representative x F m).neighborhood ⊓ (representative x G n).neighborhood

/-- The base point belongs to the common representative neighborhood. -/
theorem commonMem
    (m : PresheafOfModules.stalkModuleCatOfCommRing F x)
    (n : PresheafOfModules.stalkModuleCatOfCommRing G x) :
    x ∈ commonOpen F G x m n := sorry

/-- The base point belongs to the intersection of two representative neighborhoods. -/
theorem representativeInfMem
    {H K : PresheafOfModules (ringPresheaf R)}
    (a : Representative H x) (b : Representative K x) :
    x ∈ a.neighborhood ⊓ b.neighborhood := sorry

/-- The germ of the pure tensor of two chosen representatives on their common neighborhood. -/
noncomputable def liftPair
    (m : PresheafOfModules.stalkModuleCatOfCommRing F x)
    (n : PresheafOfModules.stalkModuleCatOfCommRing G x) : source F G x :=
  TopCat.Presheaf.germ
    (PresheafOfModules.Monoidal.tensorObj F G).presheaf
      (commonOpen F G x m n) x (commonMem F G x m n)
      (F.map (homOfLE inf_le_left).op (representative x F m).value
        ⊗ₜ[R.obj (op (commonOpen F G x m n))]
        G.map (homOfLE inf_le_right).op (representative x G n).value)

/-- `liftPair` may be computed from any neighborhood representatives of its two stalk inputs. -/
theorem liftPair_eq_germ (m : PresheafOfModules.stalkModuleCatOfCommRing F x)
    (n : PresheafOfModules.stalkModuleCatOfCommRing G x)
    (a : Representative F x)
    (ha : TopCat.Presheaf.germ F.presheaf a.neighborhood x a.memNeighborhood a.value = m)
    (b : Representative G x)
    (hb : TopCat.Presheaf.germ G.presheaf b.neighborhood x b.memNeighborhood b.value = n) :
    liftPair F G x m n =
      TopCat.Presheaf.germ
        (PresheafOfModules.Monoidal.tensorObj F G).presheaf
          (a.neighborhood ⊓ b.neighborhood) x
          (representativeInfMem x a b)
          (F.map (homOfLE inf_le_left).op a.value
            ⊗ₜ[R.obj (op (a.neighborhood ⊓ b.neighborhood))]
            G.map (homOfLE inf_le_right).op b.value) := sorry

/-- On germs represented over a common neighborhood, `liftPair` is the germ of the pointwise
pure tensor. This is the choice-independent specification of `liftPair`. -/
@[stacks 01CB "inverse tensor-stalk lift on represented germs"]
theorem liftPair_germ (U : Opens X) (hx : x ∈ U)
    (m : F.obj (op U)) (n : G.obj (op U)) :
    liftPair F G x (TopCat.Presheaf.germ F.presheaf U x hx m)
        (TopCat.Presheaf.germ G.presheaf U x hx n) =
      TopCat.Presheaf.germ
        (PresheafOfModules.Monoidal.tensorObj F G).presheaf U x hx
          (m ⊗ₜ[R.obj (op U)] n) := sorry

/-- `liftPair` preserves addition in its first stalk argument. -/
theorem liftPair_add_left
    (m m' : PresheafOfModules.stalkModuleCatOfCommRing F x)
    (n : PresheafOfModules.stalkModuleCatOfCommRing G x) :
    liftPair F G x (m + m') n = liftPair F G x m n + liftPair F G x m' n := sorry

/-- `liftPair` is linear in its first stalk argument. -/
theorem liftPair_smul_left (r : R.stalk x)
    (m : PresheafOfModules.stalkModuleCatOfCommRing F x)
    (n : PresheafOfModules.stalkModuleCatOfCommRing G x) :
    liftPair F G x (r • m) n = r • liftPair F G x m n := sorry

/-- `liftPair` preserves addition in its second stalk argument. -/
theorem liftPair_add_right
    (m : PresheafOfModules.stalkModuleCatOfCommRing F x)
    (n n' : PresheafOfModules.stalkModuleCatOfCommRing G x) :
    liftPair F G x m (n + n') = liftPair F G x m n + liftPair F G x m n' := sorry

/-- `liftPair` is linear in its second stalk argument. -/
theorem liftPair_smul_right (r : R.stalk x)
    (m : PresheafOfModules.stalkModuleCatOfCommRing F x)
    (n : PresheafOfModules.stalkModuleCatOfCommRing G x) :
    liftPair F G x m (r • n) = r • liftPair F G x m n := sorry

/-- The explicit inverse from the tensor product of the two stalks to the stalk of the pointwise
tensor product. -/
@[stacks 01CB "inverse module-presheaf tensor product stalk comparison"]
noncomputable def comparisonInv : target F G x ⟶ source F G x :=
  ModuleCat.MonoidalCategory.tensorLift
    (liftPair F G x)
    (liftPair_add_left F G x)
    (liftPair_smul_left F G x)
    (liftPair_add_right F G x)
    (liftPair_smul_right F G x)

/-- The inverse tensor-stalk comparison sends a pure tensor of germs to the germ of the
pointwise pure tensor. -/
@[stacks 01CB "inverse tensor-stalk comparison on pure tensors"]
theorem comparisonInv_germ_tmul (U : Opens X) (hx : x ∈ U)
    (m : F.obj (op U)) (n : G.obj (op U)) :
    comparisonInv F G x
        (TopCat.Presheaf.germ F.presheaf U x hx m ⊗ₜ[R.stalk x]
          TopCat.Presheaf.germ G.presheaf U x hx n) =
      TopCat.Presheaf.germ
        (PresheafOfModules.Monoidal.tensorObj F G).presheaf U x hx
          (m ⊗ₜ[R.obj (op U)] n) := sorry

/-- The tensor-stalk comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 01CB "module-presheaf tensor product stalk forward-inverse law"]
theorem comparison_hom_inv_id :
    comparison F G x ≫ comparisonInv F G x = 𝟙 _ := sorry

/-- The explicit inverse followed by the tensor-stalk comparison is the identity. -/
@[simp, stacks 01CB "module-presheaf tensor product stalk inverse-forward law"]
theorem comparison_inv_hom_id :
    comparisonInv F G x ≫ comparison F G x = 𝟙 _ := sorry

/-- The canonical isomorphism from the stalk of a pointwise tensor product to the tensor product
of the two stalk modules, with an explicitly owned inverse. -/
@[stacks 01CB "module-presheaf tensor product stalk comparison isomorphism"]
noncomputable def comparisonIso : source F G x ≅ target F G x where
  hom := comparison F G x
  inv := comparisonInv F G x
  hom_inv_id := comparison_hom_inv_id F G x
  inv_hom_id := comparison_inv_hom_id F G x

/-- Stalks commute with pointwise tensor products of module presheaves. -/
@[stacks 01CB "module-presheaf tensor product stalk comparison is an isomorphism", instance]
instance comparison_isIso : IsIso (comparison F G x) :=
  sorry

/-- The forward map of `comparisonIso` is the explicit tensor-stalk comparison. -/
@[simp, stacks 01CB "module-presheaf tensor product stalk isomorphism hom"]
theorem comparisonIso_hom : (comparisonIso F G x).hom = comparison F G x := sorry

/-- The inverse map of `comparisonIso` is the explicit tensor-stalk inverse. -/
@[simp, stacks 01CB "module-presheaf tensor product stalk isomorphism inverse"]
theorem comparisonIso_inv : (comparisonIso F G x).inv = comparisonInv F G x := sorry

/-- The presheaf tensor-stalk comparison is natural in both module arguments. -/
@[stacks 01CB "module-presheaf tensor product stalk comparison naturality"]
theorem comparison_naturality
    {F₁ F₂ G₁ G₂ : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) (x : X) :
    CommSq
      (PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.Monoidal.tensorHom f g) x)
      (comparison F₁ G₁ x)
      (comparison F₂ G₂ x)
      (PresheafOfModules.stalkMapOfCommRing f x ⊗ₘ
        PresheafOfModules.stalkMapOfCommRing g x) := sorry

/-- The explicit inverse tensor-stalk comparison is natural in both module arguments. -/
@[stacks 01CB "inverse module-presheaf tensor product stalk comparison naturality"]
theorem comparisonInv_naturality
    {F₁ F₂ G₁ G₂ : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) (x : X) :
    CommSq
      (PresheafOfModules.stalkMapOfCommRing f x ⊗ₘ
        PresheafOfModules.stalkMapOfCommRing g x)
      (comparisonInv F₁ G₁ x)
      (comparisonInv F₂ G₂ x)
      (PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.Monoidal.tensorHom f g) x) := sorry

/-- The source bifunctor for the tensor-stalk comparison. -/
@[stacks 01CB "module-presheaf tensor-stalk source bifunctor"]
noncomputable def sourceFunctor (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (PMod(ringPresheaf R) × PMod(ringPresheaf R)) ⥤ ModuleCat (R.stalk x) :=
  MonoidalCategory.tensor (PMod(ringPresheaf R)) ⋙
    PresheafOfModules.stalkFunctorOfCommRing R x

/-- The target bifunctor for the tensor-stalk comparison. -/
@[stacks 01CB "module-presheaf tensor-stalk target bifunctor"]
noncomputable def targetFunctor (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (PMod(ringPresheaf R) × PMod(ringPresheaf R)) ⥤ ModuleCat (R.stalk x) :=
  Functor.prod (PresheafOfModules.stalkFunctorOfCommRing R x)
      (PresheafOfModules.stalkFunctorOfCommRing R x) ⋙
    MonoidalCategory.tensor (ModuleCat (R.stalk x))

/-- The tensor-stalk comparison assembled as a natural transformation in both presheaf inputs. -/
@[stacks 01CB "natural tensor-stalk comparison"]
noncomputable def comparisonNatTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    sourceFunctor R x ⟶ targetFunctor R x where
  app p := comparison p.1 p.2 x
  naturality _ _ f := (comparison_naturality f.1 f.2 x).w

/-- The inverse tensor-stalk comparisons assembled as a natural transformation. -/
@[stacks 01CB "natural inverse tensor-stalk comparison"]
noncomputable def comparisonInvNatTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    targetFunctor R x ⟶ sourceFunctor R x where
  app p := comparisonInv p.1 p.2 x
  naturality _ _ f := (comparisonInv_naturality f.1 f.2 x).w

/-- The tensor-stalk comparison followed by its inverse natural transformation is the identity. -/
@[simp, stacks 01CB "module-presheaf tensor-stalk natural forward-inverse law"]
theorem comparisonNatTrans_hom_inv_id
    (R : X.Presheaf CommRingCat.{u}) (x : X) :
    comparisonNatTrans R x ≫ comparisonInvNatTrans R x = 𝟙 _ := sorry

/-- The inverse followed by the tensor-stalk comparison natural transformation is the identity. -/
@[simp, stacks 01CB "module-presheaf tensor-stalk natural inverse-forward law"]
theorem comparisonNatTrans_inv_hom_id
    (R : X.Presheaf CommRingCat.{u}) (x : X) :
    comparisonInvNatTrans R x ≫ comparisonNatTrans R x = 𝟙 _ := sorry

/-- The isomorphism-valued tensor-stalk comparison is natural in both presheaf inputs. -/
@[stacks 01CB "tensor-stalk comparison isomorphism naturality"]
theorem comparisonIso_naturality
    (R : X.Presheaf CommRingCat.{u}) (x : X)
    {p q : PMod(ringPresheaf R) × PMod(ringPresheaf R)} (f : p ⟶ q) :
    (sourceFunctor R x).map f ≫
        (comparisonIso q.1 q.2 x).hom =
      (comparisonIso p.1 p.2 x).hom ≫ (targetFunctor R x).map f := sorry

/-- The tensor-stalk comparison assembled as a natural isomorphism in both presheaf inputs. -/
@[stacks 01CB "natural tensor-stalk comparison isomorphism"]
noncomputable def comparisonNatIso (R : X.Presheaf CommRingCat.{u}) (x : X) :
    sourceFunctor R x ≅ targetFunctor R x where
  hom := comparisonNatTrans R x
  inv := comparisonInvNatTrans R x
  hom_inv_id := comparisonNatTrans_hom_inv_id R x
  inv_hom_id := comparisonNatTrans_inv_hom_id R x

/-- A component of `comparisonNatIso` is the pointwise tensor-stalk isomorphism. -/
@[simp, stacks 01CB "module-presheaf tensor-stalk natural isomorphism component"]
theorem comparisonNatIso_app
    (R : X.Presheaf CommRingCat.{u}) (x : X)
    (p : PMod(ringPresheaf R) × PMod(ringPresheaf R)) :
    (comparisonNatIso R x).app p = comparisonIso p.1 p.2 x := sorry

/-- The forward natural transformation of `comparisonNatIso` is the explicit comparison. -/
@[simp, stacks 01CB "module-presheaf tensor-stalk natural isomorphism hom"]
theorem comparisonNatIso_hom
    (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (comparisonNatIso R x).hom = comparisonNatTrans R x := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the explicit inverse. -/
@[simp, stacks 01CB "module-presheaf tensor-stalk natural isomorphism inverse"]
theorem comparisonNatIso_inv
    (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (comparisonNatIso R x).inv = comparisonInvNatTrans R x := sorry

/-- The forward component of `comparisonNatIso` is the pointwise comparison morphism. -/
@[simp, stacks 01CB "module-presheaf tensor-stalk natural isomorphism hom component"]
theorem comparisonNatIso_hom_app
    (R : X.Presheaf CommRingCat.{u}) (x : X)
    (p : PMod(ringPresheaf R) × PMod(ringPresheaf R)) :
    (comparisonNatIso R x).hom.app p = comparison p.1 p.2 x := sorry

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CB "module-presheaf tensor-stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app
    (R : X.Presheaf CommRingCat.{u}) (x : X)
    (p : PMod(ringPresheaf R) × PMod(ringPresheaf R)) :
    (comparisonNatIso R x).inv.app p = comparisonInv p.1 p.2 x := sorry

end PresheafOfModules.Tensor.Stalk
