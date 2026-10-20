module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.TensorAlgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ring-valued tensor-algebra presheaves

This file retains the multiplicative structure of the sectionwise tensor algebra.  Its
additive-group-valued presheaf is canonically identified with the one underlying the existing
module-presheaf construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules.TensorAlgebra

variable {C : Type u} [Category.{v} C]
variable (R : Cᵒᵖ ⥤ CommRingCat.{w})
variable (F : PresheafOfModules.{w} (RingPresheaf R))

/-- The tensor algebra of a module of sections, retaining its ring structure. -/
abbrev ringObj (U : Cᵒᵖ) : RingCat.{w} :=
  RingCat.of (TensorAlgebra (R.obj U) (sectionObj R F U))

/-- The multiplicative restriction map between sectionwise tensor algebras. -/
noncomputable abbrev ringMap {U V : Cᵒᵖ} (i : U ⟶ V) :
    ringObj R F U ⟶ ringObj R F V :=
  RingCat.ofHom (restrictionRingHom R F i)

/-- The ring-valued tensor-algebra restriction maps preserve identities. -/
theorem ringMap_id (U : Cᵒᵖ) :
    ringMap R F (𝟙 U) = 𝟙 (ringObj R F U) := sorry

/-- The ring-valued tensor-algebra restriction maps preserve composition. -/
theorem ringMap_comp {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    ringMap R F (i ≫ j) = ringMap R F i ≫ ringMap R F j := sorry

/-- The ring-valued sectionwise tensor-algebra presheaf. -/
@[stacks 01CH "ring-valued tensor-algebra presheaf"]
noncomputable def ringPresheaf : Cᵒᵖ ⥤ RingCat.{w} where
  obj := ringObj R F
  map := ringMap R F
  map_id := ringMap_id R F
  map_comp := ringMap_comp R F

/-- The objectwise structural ring map into the sectionwise tensor algebra. -/
noncomputable abbrev ringUnitApp (U : Cᵒᵖ) :
    (RingPresheaf R).obj U ⟶ ringObj R F U :=
  RingCat.ofHom
    (algebraMap (R.obj U) (TensorAlgebra (R.obj U) (sectionObj R F U)))

/-- The structural maps into tensor algebras commute with restriction. -/
theorem ringUnit_naturality {U V : Cᵒᵖ} (i : U ⟶ V) :
    (RingPresheaf R).map i ≫ ringUnitApp R F V =
      ringUnitApp R F U ≫ (ringPresheaf R F).map i := sorry

/-- The canonical structural map from the base ring presheaf to the tensor-algebra presheaf. -/
@[stacks 01CH "tensor-algebra presheaf structure map"]
noncomputable def ringUnit : RingPresheaf R ⟶ ringPresheaf R F where
  app := ringUnitApp R F
  naturality := fun {_ _} i ↦ ringUnit_naturality R F i

/-- Naturality of the identity comparison between the two additive tensor-algebra
presheaves. -/
@[stacks 01CH "additive tensor-algebra presheaf comparison naturality"]
theorem addCommGrpPresheafNatTrans_naturality {U V : Cᵒᵖ} (i : U ⟶ V) :
    ((ringPresheaf R F ⋙ forget₂ RingCat AddCommGrpCat).map i) ≫ 𝟙 _ =
      𝟙 _ ≫ (presheaf R F).presheaf.map i := sorry

/-- The identity components comparing the two additive tensor-algebra presheaves. -/
@[stacks 01CH "additive tensor-algebra presheaf comparison"]
noncomputable def addCommGrpPresheafNatTrans :
    ringPresheaf R F ⋙ forget₂ RingCat AddCommGrpCat ⟶
      (presheaf R F).presheaf where
  app _ := 𝟙 _
  naturality _ _ i := addCommGrpPresheafNatTrans_naturality R F i

/-- Naturality of the inverse identity comparison between the two additive
tensor-algebra presheaves. -/
@[stacks 01CH "inverse additive tensor-algebra presheaf comparison naturality"]
theorem addCommGrpPresheafInvNatTrans_naturality {U V : Cᵒᵖ} (i : U ⟶ V) :
    (presheaf R F).presheaf.map i ≫ 𝟙 _ =
      𝟙 _ ≫ (ringPresheaf R F ⋙ forget₂ RingCat AddCommGrpCat).map i := sorry

/-- The inverse identity components comparing the two additive tensor-algebra
presheaves. -/
@[stacks 01CH "inverse additive tensor-algebra presheaf comparison"]
noncomputable def addCommGrpPresheafInvNatTrans :
    (presheaf R F).presheaf ⟶
      ringPresheaf R F ⋙ forget₂ RingCat AddCommGrpCat where
  app _ := 𝟙 _
  naturality _ _ i := addCommGrpPresheafInvNatTrans_naturality R F i

/-- Each component of the additive tensor-algebra presheaf comparison is the identity. -/
@[simp, stacks 01CH "additive tensor-algebra presheaf comparison component"]
theorem addCommGrpPresheafNatTrans_app (U : Cᵒᵖ) :
    (addCommGrpPresheafNatTrans R F).app U = 𝟙 _ := sorry

/-- Each component of the inverse additive tensor-algebra presheaf comparison is the
identity. -/
@[simp, stacks 01CH "inverse additive tensor-algebra presheaf comparison component"]
theorem addCommGrpPresheafInvNatTrans_app (U : Cᵒᵖ) :
    (addCommGrpPresheafInvNatTrans R F).app U = 𝟙 _ := sorry

/-- The additive tensor-algebra presheaf comparison followed by its inverse is the
identity. -/
@[simp, stacks 01CH "additive tensor-algebra presheaf forward-inverse law"]
theorem addCommGrpPresheafNatTrans_hom_inv_id :
    addCommGrpPresheafNatTrans R F ≫ addCommGrpPresheafInvNatTrans R F = 𝟙 _ := sorry

/-- The inverse additive tensor-algebra presheaf comparison followed by the forward
comparison is the identity. -/
@[simp, stacks 01CH "additive tensor-algebra presheaf inverse-forward law"]
theorem addCommGrpPresheafNatTrans_inv_hom_id :
    addCommGrpPresheafInvNatTrans R F ≫ addCommGrpPresheafNatTrans R F = 𝟙 _ := sorry

/-- Forgetting multiplication from the ring-valued tensor-algebra presheaf recovers the
additive presheaf underlying the module-valued tensor algebra. -/
@[stacks 01CH "additive tensor-algebra presheaf comparison isomorphism"]
noncomputable def addCommGrpPresheafIso :
    ringPresheaf R F ⋙ forget₂ RingCat AddCommGrpCat ≅
      (presheaf R F).presheaf where
  hom := addCommGrpPresheafNatTrans R F
  inv := addCommGrpPresheafInvNatTrans R F
  hom_inv_id := addCommGrpPresheafNatTrans_hom_inv_id R F
  inv_hom_id := addCommGrpPresheafNatTrans_inv_hom_id R F

/-- The forward map of the additive tensor-algebra presheaf isomorphism is the explicit
identity comparison. -/
@[simp, stacks 01CH "additive tensor-algebra presheaf isomorphism hom"]
theorem addCommGrpPresheafIso_hom :
    (addCommGrpPresheafIso R F).hom = addCommGrpPresheafNatTrans R F := sorry

/-- The inverse map of the additive tensor-algebra presheaf isomorphism is the explicit
inverse identity comparison. -/
@[simp, stacks 01CH "additive tensor-algebra presheaf isomorphism inverse"]
theorem addCommGrpPresheafIso_inv :
    (addCommGrpPresheafIso R F).inv = addCommGrpPresheafInvNatTrans R F := sorry

/-- A component of the additive tensor-algebra presheaf isomorphism is the identity
isomorphism. -/
@[simp, stacks 01CH "additive tensor-algebra presheaf isomorphism component"]
theorem addCommGrpPresheafIso_app (U : Cᵒᵖ) :
    (addCommGrpPresheafIso R F).app U =
      Iso.refl ((presheaf R F).presheaf.obj U) := sorry

/-- A forward component of the additive tensor-algebra presheaf isomorphism is the
identity morphism. -/
@[simp, stacks 01CH "additive tensor-algebra presheaf isomorphism hom component"]
theorem addCommGrpPresheafIso_hom_app (U : Cᵒᵖ) :
    (addCommGrpPresheafIso R F).hom.app U = 𝟙 _ := sorry

/-- An inverse component of the additive tensor-algebra presheaf isomorphism is the
identity morphism. -/
@[simp, stacks 01CH "additive tensor-algebra presheaf isomorphism inverse component"]
theorem addCommGrpPresheafIso_inv_app (U : Cᵒᵖ) :
    (addCommGrpPresheafIso R F).inv.app U = 𝟙 _ := sorry

end PresheafOfModules.TensorAlgebra
