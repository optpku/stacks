/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
public import ReasLib.Topology.Sheaf.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaf cohomology under a continuous map

This leaf owns the comparison maps on objectwise cohomology induced by inverse and direct image
of abelian sheaves.  The fundamental construction is the map on `Ext` induced by exact inverse
image.  Its source is identified using the canonical pullback isomorphism for sheafified free
abelian Yoneda objects.

For a general continuous map, direct-image cohomology on `U` need not agree with cohomology on
`f ⁻¹' U` in positive degree.  Accordingly, the reusable interface exposes a comparison map in
all degrees and records that this comparison is invertible in degree zero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace TopCat
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace CategoryTheory.Sheaf

variable {X Y : TopCat.{u}}

section Pullback

/-- The map on cohomology over an open induced by inverse image along a continuous map.  It is
the map on `Ext` induced by exact pullback, precomposed with the canonical free abelian Yoneda
pullback isomorphism. -/
noncomputable def pullbackCohomologyMap
    (f : X ⟶ Y) (G : Y.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    G.H' p U ⟶
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G).H' p ((Opens.map f).obj U) :=
  AddCommGrpCat.ofHom <|
    ((Ext.mk₀ (TopCat.Sheaf.FreeAbelianYoneda.pullbackIso f U).hom).precomp
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G) (zero_add p)).comp
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).mapExtAddHom
          (GrothendieckTopology.FreeAbelianYoneda.obj
            (Opens.grothendieckTopology Y) U) G p)

set_option backward.isDefEq.respectTransparency false in
/-- Pullback on objectwise cohomology, bundled as a morphism of presheaves. -/
noncomputable def pullbackCohomology
    (f : X ⟶ Y) (G : Y.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    G.cohomologyPresheaf p ⟶
      (Opens.map f).op ⋙
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G).cohomologyPresheaf p where
  app U := pullbackCohomologyMap f G p U.unop
  naturality {U V} i := by
    ext e
    change (Ext.mk₀ (TopCat.Sheaf.FreeAbelianYoneda.pullbackIso f V.unop).hom).comp
        (((Ext.mk₀ (GrothendieckTopology.FreeAbelianYoneda.map
          (Opens.grothendieckTopology Y) i.unop)).comp e (zero_add p)).mapExactFunctor
            (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)) (zero_add p) =
      (Ext.mk₀ (GrothendieckTopology.FreeAbelianYoneda.map
        (Opens.grothendieckTopology X) ((Opens.map f).map i.unop))).comp
          ((Ext.mk₀ (TopCat.Sheaf.FreeAbelianYoneda.pullbackIso f U.unop).hom).comp
            (e.mapExactFunctor (TopCat.Sheaf.pullback AddCommGrpCat.{u} f))
              (zero_add p)) (zero_add p)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    simp only [Ext.mk₀_comp_mk₀_assoc]
    rw [← TopCat.Sheaf.FreeAbelianYoneda.pullbackIso_naturality f i.unop]

/-- The component of the pullback morphism of cohomology presheaves is
`pullbackCohomologyMap`. -/
theorem pullbackCohomology_app
    (f : X ⟶ Y) (G : Y.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    (pullbackCohomology f G p).app (op U) = pullbackCohomologyMap f G p U := rfl

/-- Pullback on cohomology commutes with restriction along an inclusion of opens. -/
theorem pullbackCohomologyMap_naturality
    (f : X ⟶ Y) (G : Y.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    {U V : Opens Y} (i : U ⟶ V) :
    (G.cohomologyPresheaf p).map i.op ≫ pullbackCohomologyMap f G p U =
      pullbackCohomologyMap f G p V ≫
        (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G).cohomologyPresheaf p).map
          ((Opens.map f).map i).op :=
  (pullbackCohomology f G p).naturality i.op

set_option backward.isDefEq.respectTransparency false in
/-- Pullback on cohomology is natural in the coefficient sheaf. -/
theorem pullbackCohomologyMap_map
    (f : X ⟶ Y) {G H : Y.Sheaf AddCommGrpCat.{u}} (g : G ⟶ H)
    (p : ℕ) (U : Opens Y) :
    cohomologyMap g p U ≫ pullbackCohomologyMap f H p U =
      pullbackCohomologyMap f G p U ≫
        cohomologyMap ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map g) p
          ((Opens.map f).obj U) := by
  ext e
  change (Ext.mk₀ (TopCat.Sheaf.FreeAbelianYoneda.pullbackIso f U).hom).comp
      ((e.comp (Ext.mk₀ g) (add_zero p)).mapExactFunctor
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)) (zero_add p) =
    ((Ext.mk₀ (TopCat.Sheaf.FreeAbelianYoneda.pullbackIso f U).hom).comp
      (e.mapExactFunctor (TopCat.Sheaf.pullback AddCommGrpCat.{u} f))
        (zero_add p)).comp
          (Ext.mk₀ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map g)) (add_zero p)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

end Pullback

section Pushforward

/-- The canonical comparison from cohomology of a direct image over `U` to cohomology of the
original sheaf over `(Opens.map f).obj U`.  It is pullback on `Ext`, followed by the adjunction
counit on coefficients. -/
noncomputable def pushforwardCohomologyMap
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).H' p U ⟶
      F.H' p ((Opens.map f).obj U) :=
  pullbackCohomologyMap f ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) p U ≫
    cohomologyMap
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).counit.app F) p
      ((Opens.map f).obj U)

/-- The defining factorization of the pushforward cohomology comparison. -/
theorem pushforwardCohomologyMap_def
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    pushforwardCohomologyMap f F p U =
      pullbackCohomologyMap f ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) p U ≫
        cohomologyMap
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).counit.app F) p
          ((Opens.map f).obj U) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The direct-image comparison, bundled as a morphism of cohomology presheaves. -/
noncomputable def pushforwardCohomology
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).cohomologyPresheaf p ⟶
      (Opens.map f).op ⋙ F.cohomologyPresheaf p where
  app U := pushforwardCohomologyMap f F p U.unop
  naturality {_U _V} i :=
    (pullbackCohomology f ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) p ≫
      Functor.whiskerLeft (Opens.map f).op
        ((cohomologyPresheafFunctor (Opens.grothendieckTopology X) p).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).counit.app F))).naturality i

/-- The component of the pushforward comparison of cohomology presheaves is
`pushforwardCohomologyMap`. -/
theorem pushforwardCohomology_app
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    (pushforwardCohomology f F p).app (op U) = pushforwardCohomologyMap f F p U := rfl

/-- If direct image along `f` is exact, its cohomology comparison over every open is an
isomorphism in every degree.  Exactness is an explicit hypothesis so this theorem also applies
beyond geometric closed embeddings. -/
@[stacks 02UV "exact direct-image comparison"]
theorem pushforwardCohomologyMap_isIso_of_exact
    (f : X ⟶ Y)
    (hf : exactFunctor (X.Sheaf AddCommGrpCat.{u}) (Y.Sheaf AddCommGrpCat.{u})
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    IsIso (pushforwardCohomologyMap f F p U) := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Pullback on cohomology factors through the adjunction unit and the direct-image
comparison. -/
theorem cohomologyMap_unit_comp
    (f : X ⟶ Y) (G : Y.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    cohomologyMap
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app G) p U ≫
      pushforwardCohomologyMap f
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G) p U =
      pullbackCohomologyMap f G p U := by
  let L := TopCat.Sheaf.pullback AddCommGrpCat.{u} f
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f
  let η := adj.unit.app G
  let ε := adj.counit.app (L.obj G)
  let V := (Opens.map f).obj U
  let H := cohomologyPresheafFunctor (Opens.grothendieckTopology X) p
  have hnat := pullbackCohomologyMap_map f η p U
  have hcomp : cohomologyMap (L.map η ≫ ε) p V =
      cohomologyMap (L.map η) p V ≫ cohomologyMap ε p V :=
    congrArg (fun α ↦ α.app (op V)) (H.map_comp (L.map η) ε)
  have htri : cohomologyMap (L.map η ≫ ε) p V = 𝟙 _ :=
    (congrArg (fun g ↦ cohomologyMap g p V) (adj.left_triangle_components G)).trans
      (congrArg (fun α ↦ α.app (op V)) (H.map_id (L.obj G)))
  change cohomologyMap η p U ≫
      (pullbackCohomologyMap f
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (L.obj G)) p U ≫
          cohomologyMap ε p V) = _
  erw [← Category.assoc, hnat, Category.assoc, ← hcomp, htri, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In degree zero, direct-image cohomology over an open agrees with cohomology of the original
sheaf over the inverse-image open. -/
noncomputable instance pushforwardCohomologyMap_isIso_zero
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (U : Opens Y) :
    IsIso (pushforwardCohomologyMap f F 0 U) := by
  let i := TopCat.Sheaf.FreeAbelianYoneda.pullbackIso f U
  let e : (GrothendieckTopology.FreeAbelianYoneda.obj
      (Opens.grothendieckTopology Y) U ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) ≃
      (GrothendieckTopology.FreeAbelianYoneda.obj
        (Opens.grothendieckTopology X) ((Opens.map f).obj U) ⟶ F) :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ _).symm.trans
      { toFun := fun a ↦ i.hom ≫ a
        invFun := fun a ↦ i.inv ≫ a
        left_inv := fun a ↦ i.inv_hom_id_assoc a
        right_inv := fun a ↦ i.hom_inv_id_assoc a }
  have hmap (a : GrothendieckTopology.FreeAbelianYoneda.obj
      (Opens.grothendieckTopology Y) U ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) :
      pushforwardCohomologyMap f F 0 U (Ext.mk₀ a) = Ext.mk₀ (e a) := by
    change ((Ext.mk₀ i.hom).comp
      ((Ext.mk₀ a).mapExactFunctor (TopCat.Sheaf.pullback AddCommGrpCat.{u} f))
        (zero_add 0)).comp
          (Ext.mk₀
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).counit.app F))
              (add_zero 0) = _
    simp only [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    change Ext.mk₀ ((i.hom ≫ (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map a) ≫ _) =
      Ext.mk₀ (i.hom ≫ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map a ≫ _))
    rw [Category.assoc]
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro a b h
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).2 a
    obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective _ _).2 b
    rw [hmap, hmap] at h
    exact congrArg Ext.mk₀ (e.injective ((Ext.mk₀_bijective _ _).1 h))
  · intro a
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).2 a
    exact ⟨Ext.mk₀ (e.symm a), (hmap _).trans (congrArg Ext.mk₀ (e.apply_symm_apply a))⟩

end Pushforward

end CategoryTheory.Sheaf

/- Audit the core cohomology constructions. -/
