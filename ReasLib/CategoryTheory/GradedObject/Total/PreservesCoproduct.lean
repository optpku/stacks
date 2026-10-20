/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import ReasLib.CategoryTheory.GradedObject.Total.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Totalization and coproduct-preserving functors

A functor preserving `I`-indexed coproducts commutes canonically with totalization of
`I`-graded objects. The comparison is exposed as a natural isomorphism together with its
homogeneous-summand formula.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.GradedObject.Total

variable {I : Type w}
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable [HasCoproductsOfShape I C] [HasCoproductsOfShape I D]

/-- Naturality of the coproduct-preservation comparison for total graded objects. -/
theorem mapIso_naturality (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L]
    {X Y : GradedObject I C} (f : X ⟶ Y) :
    L.map (Limits.Sigma.map f) ≫ (PreservesCoproduct.iso L Y).hom =
      (PreservesCoproduct.iso L X).hom ≫
        Limits.Sigma.map (fun i : I ↦ L.map (f i)) := sorry

/-- Naturality of the inverse coproduct-preservation comparison for total graded objects. -/
@[stacks 01CF "inverse totalization comparison naturality"]
theorem mapIso_inv_naturality (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L]
    {X Y : GradedObject I C} (f : X ⟶ Y) :
    Limits.Sigma.map (fun i : I ↦ L.map (f i)) ≫ (PreservesCoproduct.iso L Y).inv =
      (PreservesCoproduct.iso L X).inv ≫ L.map (Limits.Sigma.map f) := sorry

/-- The forward coproduct-preservation comparisons form the totalization natural transformation. -/
@[stacks 01CF "totalization comparison natural transformation"]
noncomputable def mapNatTrans (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] :
    functor (I := I) (C := C) ⋙ L ⟶
      Functor.pi (fun _ : I ↦ L) ⋙ functor (I := I) (C := D) where
  app X := (PreservesCoproduct.iso L X).hom
  naturality _ _ f := mapIso_naturality L f

/-- The inverse coproduct-preservation comparisons form the inverse totalization natural
transformation. -/
@[stacks 01CF "inverse totalization comparison natural transformation"]
noncomputable def mapNatTransInv (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] :
    Functor.pi (fun _ : I ↦ L) ⋙ functor (I := I) (C := D) ⟶
      functor (I := I) (C := C) ⋙ L where
  app X := (PreservesCoproduct.iso L X).inv
  naturality _ _ f := mapIso_inv_naturality L f

/-- A component of the forward totalization comparison is the canonical coproduct comparison. -/
@[simp, stacks 01CF "totalization comparison natural transformation component"]
theorem mapNatTrans_app (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] (X : GradedObject I C) :
    (mapNatTrans (I := I) L).app X = (PreservesCoproduct.iso L X).hom := sorry

/-- A component of the inverse totalization comparison is the inverse coproduct comparison. -/
@[simp, stacks 01CF "inverse totalization comparison natural transformation component"]
theorem mapNatTransInv_app (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] (X : GradedObject I C) :
    (mapNatTransInv (I := I) L).app X = (PreservesCoproduct.iso L X).inv := sorry

/-- The forward and inverse totalization natural transformations compose to the identity. -/
@[simp, stacks 01CF "totalization comparison forward-inverse law"]
theorem mapNatTrans_hom_inv_id (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] :
    mapNatTrans (I := I) L ≫ mapNatTransInv (I := I) L = 𝟙 _ := sorry

/-- The inverse and forward totalization natural transformations compose to the identity. -/
@[simp, stacks 01CF "totalization comparison inverse-forward law"]
theorem mapNatTrans_inv_hom_id (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] :
    mapNatTransInv (I := I) L ≫ mapNatTrans (I := I) L = 𝟙 _ := sorry

/-- The forward and inverse totalization comparison components compose to the identity. -/
@[simp, stacks 01CF "totalization comparison component forward-inverse law"]
theorem mapNatTrans_app_comp_inv_app (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] (X : GradedObject I C) :
    (mapNatTrans (I := I) L).app X ≫ (mapNatTransInv (I := I) L).app X = 𝟙 _ := sorry

/-- The inverse and forward totalization comparison components compose to the identity. -/
@[simp, stacks 01CF "totalization comparison component inverse-forward law"]
theorem mapNatTransInv_app_comp_app (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] (X : GradedObject I C) :
    (mapNatTransInv (I := I) L).app X ≫ (mapNatTrans (I := I) L).app X = 𝟙 _ := sorry

/-- A coproduct-preserving functor commutes naturally with totalization. -/
@[stacks 01CF "totalization commutes with coproduct-preserving functors"]
noncomputable def mapIso (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] :
    functor (I := I) (C := C) ⋙ L ≅
      Functor.pi (fun _ : I ↦ L) ⋙ functor (I := I) (C := D) :=
  { hom := mapNatTrans (I := I) L
    inv := mapNatTransInv (I := I) L
    hom_inv_id := mapNatTrans_hom_inv_id (I := I) L
    inv_hom_id := mapNatTrans_inv_hom_id (I := I) L }

/-- The forward natural transformation of `mapIso` is the named totalization comparison. -/
@[simp, stacks 01CF "totalization comparison natural isomorphism hom"]
theorem mapIso_hom (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] :
    (mapIso (I := I) L).hom = mapNatTrans (I := I) L := sorry

/-- The inverse natural transformation of `mapIso` is the named inverse comparison. -/
@[simp, stacks 01CF "totalization comparison natural isomorphism inverse"]
theorem mapIso_inv (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] :
    (mapIso (I := I) L).inv = mapNatTransInv (I := I) L := sorry

/-- The component of `mapIso` is the canonical coproduct-preservation isomorphism. -/
@[simp, stacks 01CF "totalization comparison natural isomorphism component"]
theorem mapIso_app (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] (X : GradedObject I C) :
    (mapIso (I := I) L).app X = PreservesCoproduct.iso L X := sorry

/-- The component of `mapIso` is the canonical coproduct-preservation isomorphism. -/
@[simp]
theorem mapIso_hom_app (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] (X : GradedObject I C) :
    (mapIso (I := I) L).hom.app X =
      (PreservesCoproduct.iso L X).hom := sorry

/-- The inverse component of `mapIso` is the inverse coproduct-preservation comparison. -/
@[simp, stacks 01CF "totalization comparison natural isomorphism inverse component"]
theorem mapIso_inv_app (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L] (X : GradedObject I C) :
    (mapIso (I := I) L).inv.app X =
      (PreservesCoproduct.iso L X).inv := sorry

/-- On a homogeneous summand, the totalization comparison is the target coproduct inclusion. -/
@[reassoc (attr := simp)]
theorem map_ι_mapIso_hom (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L]
    (X : GradedObject I C) (i : I) :
    L.map (Limits.Sigma.ι X i) ≫ (mapIso (I := I) L).hom.app X =
      Limits.Sigma.ι (fun i : I ↦ L.obj (X i)) i := sorry

/-- On a homogeneous summand, the inverse totalization comparison recovers the image of the
source coproduct inclusion. -/
@[reassoc (attr := simp), stacks 01CF "inverse totalization comparison on a summand"]
theorem ι_mapIso_inv (L : C ⥤ D)
    [PreservesColimitsOfShape (Discrete I) L]
    (X : GradedObject I C) (i : I) :
    Limits.Sigma.ι (fun i : I ↦ L.obj (X i)) i ≫
        (mapIso (I := I) L).inv.app X =
      L.map (Limits.Sigma.ι X i) := sorry

end CategoryTheory.GradedObject.Total
