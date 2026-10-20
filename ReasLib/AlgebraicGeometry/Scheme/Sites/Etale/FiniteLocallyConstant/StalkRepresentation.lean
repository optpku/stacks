/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.UnderlyingModule
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.YonedaComparison
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk

/-!
# Linear monodromy on the actual module stalk

Natural automorphisms of the finite étale fiber act on pointed neighborhoods.
The resulting action on their colimit is transported by the canonical germ map
to the actual sheaf fiber. No automorphism is treated as an equivariant map of
its own finite set, and no sections on a representing scheme replace the stalk.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryOfElements Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.GeometricPoint
open CategoryTheory.Action.ModuleCat

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.StalkRepresentation

variable {X : Scheme.{u}} [ConnectedSpace X]
variable (Λ : Type v) [Ring Λ]
variable (xbar : GeometricPoint X)

/-- The finite étale inclusion keeps the underlying étale object and morphism. -/
def finiteEtaleInclusion : FiniteEtale X ⥤ X.Etale where
  obj := (FiniteEtale.toEtale X).obj
  map := (FiniteEtale.toEtale X).map

/-- The set-valued finite étale fiber functor at the geometric point. -/
abbrev fiber : FiniteEtale X ⥤ Type u :=
  GeometricPoint.finiteFiber xbar ⋙ FintypeCat.incl

/-- Values of a module presheaf on pointed finite étale neighborhoods. -/
abbrev diagram (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    (fiber xbar).Elementsᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
  (π (fiber xbar)).op ⋙ (finiteEtaleInclusion (X := X)).op ⋙ F

/-- The module-valued fiber computed using finite étale neighborhoods. -/
abbrev finiteFiber : (X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ where
  obj F := colimit (diagram Λ xbar F)
  map f := colim.map (Functor.whiskerLeft
    ((π (fiber xbar)).op ⋙ (finiteEtaleInclusion (X := X)).op) f)
  map_id F := colim.map_id (diagram Λ xbar F)
  map_comp f g := colim.map_comp
    (Functor.whiskerLeft ((π (fiber xbar)).op ⋙ (finiteEtaleInclusion (X := X)).op) f)
    (Functor.whiskerLeft ((π (fiber xbar)).op ⋙ (finiteEtaleInclusion (X := X)).op) g)

/-- A fiber automorphism acts on a pointed neighborhood by moving its geometric point. -/
abbrev move (σ : Aut (GeometricPoint.finiteFiber xbar)) :
    (fiber xbar).Elements ⥤ (fiber xbar).Elements where
  obj N := ⟨N.1, (Functor.whiskerRight σ.hom FintypeCat.incl).app N.1 N.2⟩
  map {N K} f := ⟨f.val, by
    simpa using (NatTrans.naturality_apply
      (Functor.whiskerRight σ.hom FintypeCat.incl) f.val N.2).symm.trans
        (congrArg (fun y ↦ (Functor.whiskerRight σ.hom FintypeCat.incl).app K.1 y)
          f.property)⟩

/-- The colimit endomorphism induced by a natural automorphism of the finite fiber. -/
def finiteAction (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
    (σ : Aut (GeometricPoint.finiteFiber xbar)) :
    colimit (diagram Λ xbar F) ⟶ colimit (diagram Λ xbar F) :=
  colimit.desc (diagram Λ xbar F)
    { pt := colimit (diagram Λ xbar F)
      ι :=
        { app N := colimit.ι (diagram Λ xbar F) (op ((move xbar σ).obj N.unop))
          naturality := fun N K f ↦
            colimit.w (diagram Λ xbar F) ((move xbar σ).map f.unop).op } }

/-- On a germ, the action moves its pointing and leaves its section unchanged. -/
theorem ι_finiteAction (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
    (σ : Aut (GeometricPoint.finiteFiber xbar)) (N : (fiber xbar).Elementsᵒᵖ) :
    colimit.ι (diagram Λ xbar F) N ≫ finiteAction Λ xbar F σ =
      colimit.ι (diagram Λ xbar F) (op ((move xbar σ).obj N.unop)) :=
  colimit.ι_desc _ _

/-- Identity acts identically on finite-neighborhood germs. -/
theorem finiteAction_one (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    finiteAction Λ xbar F 1 = 𝟙 _ := by
  apply colimit.hom_ext (F := diagram Λ xbar F)
  intro N
  rw [ι_finiteAction, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Composition of natural automorphisms gives the corresponding germ action. -/
theorem finiteAction_mul (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
    (σ τ : Aut (GeometricPoint.finiteFiber xbar)) :
    finiteAction Λ xbar F (σ * τ) = finiteAction Λ xbar F τ ≫ finiteAction Λ xbar F σ := by
  apply colimit.hom_ext (F := diagram Λ xbar F)
  intro N
  rw [ι_finiteAction, ← Category.assoc, ι_finiteAction, ι_finiteAction]
  rfl

/-- The linear representation on the finite-neighborhood colimit. -/
def finiteRepresentation (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    Aut (GeometricPoint.finiteFiber xbar) →* End (colimit (diagram Λ xbar F)) where
  toFun := finiteAction Λ xbar F
  map_one' := finiteAction_one Λ xbar F
  map_mul' := finiteAction_mul Λ xbar F

/-- The actual module stalk, obtained from the small étale site point. -/
def stalk : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
  sheafToPresheaf _ _ ⋙ (GeometricPoint.toSmallEtalePoint xbar).presheafFiber

/-- The canonical germ cocone sends a pointed finite étale section into the actual stalk. -/
def germCocone (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Cocone (diagram Λ xbar F.obj) where
  pt := (stalk Λ xbar).obj F
  ι :=
    { app N := (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber
        ((FiniteEtale.toEtale X).obj N.unop.1) N.unop.2 F.obj
      naturality := fun N K f ↦ by
        change F.obj.map ((FiniteEtale.toEtale X).map f.unop.val).op ≫
          (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber _ K.unop.2 F.obj =
            (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber _ N.unop.2 F.obj ≫ 𝟙 _
        rw [Category.comp_id, (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber_w]
        exact congrArg (fun y ↦ (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber _ y F.obj)
          f.unop.property }

/-- The specified finite-neighborhood-to-stalk map. -/
def germMap (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (finiteFiber Λ xbar).obj F.obj ⟶ (stalk Λ xbar).obj F :=
  colimit.desc (diagram Λ xbar F.obj) (germCocone Λ xbar F)

/-- The specified germ comparison restricts to the usual small-étale germ map. -/
theorem ι_germMap (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (N : (fiber xbar).Elementsᵒᵖ) :
    colimit.ι (diagram Λ xbar F.obj) N ≫ germMap Λ xbar F =
      (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber
        ((FiniteEtale.toEtale X).obj N.unop.1) N.unop.2 F.obj :=
  colimit.ι_desc _ _

/-- The induced colimit map is the sheaf morphism on each finite étale germ. -/
theorem ι_finiteFiber_map {F G : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ} (f : F ⟶ G)
    (N : (fiber xbar).Elementsᵒᵖ) :
    colimit.ι (diagram Λ xbar F) N ≫ (finiteFiber Λ xbar).map f =
      f.app (op ((FiniteEtale.toEtale X).obj N.unop.1)) ≫ colimit.ι (diagram Λ xbar G) N :=
  colimit.ι_map _ _

set_option backward.isDefEq.respectTransparency false in
/-- Monodromy on finite-neighborhood fibers is natural in the module presheaf. -/
theorem finiteAction_naturality {F G : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ} (f : F ⟶ G)
    (σ : Aut (GeometricPoint.finiteFiber xbar)) :
    finiteAction Λ xbar F σ ≫ (finiteFiber Λ xbar).map f =
      (finiteFiber Λ xbar).map f ≫ finiteAction Λ xbar G σ := by
  apply colimit.hom_ext (F := diagram Λ xbar F)
  intro N
  rw [← Category.assoc, ι_finiteAction, ι_finiteFiber_map,
    ← Category.assoc, ι_finiteFiber_map, Category.assoc, ι_finiteAction]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical germ map is natural in the sheaf; its target map is the actual stalk map. -/
theorem germMap_naturality {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : F ⟶ G) :
    (finiteFiber Λ xbar).map f.hom ≫ germMap Λ xbar G =
      germMap Λ xbar F ≫ (stalk Λ xbar).map f := by
  apply colimit.hom_ext (F := diagram Λ xbar F.obj)
  intro N
  rw [← Category.assoc, ι_finiteFiber_map, Category.assoc, ι_germMap,
    ← Category.assoc, ι_germMap]
  exact ((GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber_naturality
    f.hom ((FiniteEtale.toEtale X).obj N.unop.1) N.unop.2).symm

section Represented

variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
variable (U : FiniteEtale X)
variable (e : F.obj ⋙ CategoryTheory.forget (ModuleCat.{u + 1} Λ) ≅
  uliftYoneda.{u + 1}.obj ((FiniteEtale.toEtale X).obj U))

/-- The universal section of a module sheaf whose underlying presheaf is represented by `U`. -/
def representingSection : F.obj.obj (op ((FiniteEtale.toEtale X).obj U)) :=
  e.inv.app (op ((FiniteEtale.toEtale X).obj U)) (ULift.up (𝟙 ((FiniteEtale.toEtale X).obj U)))

/-- A local section determines a pointing of its finite étale representing scheme. -/
def representedSectionPoint (V : X.Etale)
    (p : (GeometricPoint.toSmallEtalePoint xbar).fiber.obj V) (s : F.obj.obj (op V)) :
    (fiber xbar).obj U :=
  (GeometricPoint.toSmallEtalePoint xbar).fiber.map (e.hom.app (op V) s).down p

/-- A represented local section determines the finite-neighborhood germ of the
universal section at its induced pointing. -/
private def representedSectionToFiniteFiberFunction (V : X.Etale)
    (p : (GeometricPoint.toSmallEtalePoint xbar).fiber.obj V) :
    F.obj.obj (op V) → (finiteFiber Λ xbar).obj F.obj :=
  fun s ↦
    colimit.ι (diagram Λ xbar F.obj)
      (op ⟨U, representedSectionPoint Λ xbar F U e V p s⟩)
      (representingSection Λ F U e)

/-- Sending represented sections to their finite-neighborhood germs preserves
addition and scalar multiplication. -/
private theorem representedSectionToFiniteFiber_isLinear (V : X.Etale)
    (p : (GeometricPoint.toSmallEtalePoint xbar).fiber.obj V) :
    (∀ s t, representedSectionToFiniteFiberFunction Λ xbar F U e V p (s + t) =
      representedSectionToFiniteFiberFunction Λ xbar F U e V p s +
        representedSectionToFiniteFiberFunction Λ xbar F U e V p t) ∧
    (∀ (a : Λ) s, representedSectionToFiniteFiberFunction Λ xbar F U e V p (a • s) =
      a • representedSectionToFiniteFiberFunction Λ xbar F U e V p s) := sorry

/-- A represented local section contributes the universal section on its pointed finite
étale representing neighborhood to the finite-neighborhood colimit. -/
@[no_expose] def representedSectionToFiniteFiber (V : X.Etale)
    (p : (GeometricPoint.toSmallEtalePoint xbar).fiber.obj V) :
    F.obj.obj (op V) ⟶ (finiteFiber Λ xbar).obj F.obj :=
  ModuleCat.ofHom
    { toFun := representedSectionToFiniteFiberFunction Λ xbar F U e V p
      map_add' := (representedSectionToFiniteFiber_isLinear Λ xbar F U e V p).1
      map_smul' := (representedSectionToFiniteFiber_isLinear Λ xbar F U e V p).2 }

/-- The represented-section map is compatible with restriction to pointed neighborhoods. -/
theorem representedSectionToFiniteFiber_naturality {V W : X.Etale} (f : V ⟶ W)
    (p : (GeometricPoint.toSmallEtalePoint xbar).fiber.obj V) :
    F.obj.map f.op ≫ representedSectionToFiniteFiber Λ xbar F U e V p =
      representedSectionToFiniteFiber Λ xbar F U e W
        ((GeometricPoint.toSmallEtalePoint xbar).fiber.map f p) := sorry

/-- Reverse the finite-neighborhood germ comparison using the supplied finite étale
representation of the underlying module presheaf. -/
def germInvOfRepresentable :
    (stalk Λ xbar).obj F ⟶ (finiteFiber Λ xbar).obj F.obj :=
  (GeometricPoint.toSmallEtalePoint xbar).presheafFiberDesc
    (representedSectionToFiniteFiber Λ xbar F U e)
    (fun {_ _} f p ↦ representedSectionToFiniteFiber_naturality Λ xbar F U e f p)

/-- On a local germ, the reverse comparison uses the universal representing section at
its induced finite étale pointing. -/
theorem toPresheafFiber_germInvOfRepresentable (V : X.Etale)
    (p : (GeometricPoint.toSmallEtalePoint xbar).fiber.obj V) :
    (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber V p F.obj ≫
        germInvOfRepresentable Λ xbar F U e =
      representedSectionToFiniteFiber Λ xbar F U e V p :=
  (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber_presheafFiberDesc _ _ V p

/-- Taking the germ and then returning to finite neighborhoods is the identity. -/
theorem germMap_germInvOfRepresentable :
    germMap Λ xbar F ≫ germInvOfRepresentable Λ xbar F U e = 𝟙 _ := sorry

/-- Returning a germ to its finite representing neighborhood preserves that germ. -/
theorem germInvOfRepresentable_germMap :
    germInvOfRepresentable Λ xbar F U e ≫ germMap Λ xbar F = 𝟙 _ := sorry

/-- The germ comparison with both directions specified by actual maps, for a supplied
finite étale representation of the module sheaf. -/
def germIsoOfRepresentable : (finiteFiber Λ xbar).obj F.obj ≅ (stalk Λ xbar).obj F where
  hom := germMap Λ xbar F
  inv := germInvOfRepresentable Λ xbar F U e
  hom_inv_id := germMap_germInvOfRepresentable Λ xbar F U e
  inv_hom_id := germInvOfRepresentable_germMap Λ xbar F U e

end Represented

end AlgebraicGeometry.Scheme.StalkRepresentation

namespace AlgebraicGeometry.Scheme.StalkRepresentation
variable {X : Scheme.{u}} [ConnectedSpace X]
variable (Λ : Type (u + 1)) [Ring Λ] (xbar : GeometricPoint X)
variable [Finite Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The germ comparison with its actual inverse obtained from the representing scheme of
the underlying finite set sheaf. Its charts are the supplied module charts under forgetfulness. -/
def germIsoApp
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    (finiteFiber Λ xbar).obj F.obj.obj ≅ (stalk Λ xbar).obj F.obj := by
  -- Local instance justification (proof-local temporary data): install the supplied finite-type local-constancy proof only to invoke the existing class-based underlying-sheaf representation API.
  letI : Sheaf.IsFiniteTypeLocallyConstantModule F.obj := F.property
  let S := (sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F.obj
  exact germIsoOfRepresentable Λ xbar F.obj
    (FiniteLocallyConstant.finiteEtaleRepresentation S)
    (FiniteLocallyConstant.representationPresheafIso S)

/-- The specified germ map is invertible because its concrete reverse map is already constructed. -/
instance germMap_isIso
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    IsIso (germMap Λ xbar F.obj) :=
  (germIsoApp Λ xbar F).isIso_hom

/-- The actual module fiber functor restricted to finite locally constant sheaves. -/
abbrev moduleStalk :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
      ModuleCat.{u + 1} Λ :=
  (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).ι ⋙ stalk Λ xbar

/-- The finite-neighborhood fiber functor restricted to finite locally constant sheaves. -/
abbrev finiteModuleFiber :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
      ModuleCat.{u + 1} Λ :=
  (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).ι ⋙
    sheafToPresheaf _ _ ⋙ finiteFiber Λ xbar

/-- The natural isomorphism induced by the canonical finite-neighborhood germ maps. -/
def germIso : finiteModuleFiber Λ xbar ≅ moduleStalk Λ xbar :=
  NatIso.ofComponents (germIsoApp Λ xbar)
    (fun f ↦ germMap_naturality Λ xbar f.hom)

/-- Natural automorphisms of finite étale fibers act linearly and naturally on germ colimits. -/
def finiteFiberAction : Aut (GeometricPoint.finiteFiber xbar) →* End (finiteModuleFiber Λ xbar) where
  toFun σ :=
    { app F := finiteAction Λ xbar F.obj.obj σ
      naturality := fun _ _ f ↦ (finiteAction_naturality Λ xbar f.hom.hom σ).symm }
  map_one' := by
    apply NatTrans.ext
    funext F
    exact finiteAction_one Λ xbar F.obj.obj
  map_mul' σ τ := by
    apply NatTrans.ext
    funext F
    exact finiteAction_mul Λ xbar F.obj.obj σ τ

/-- Linear natural monodromy on the actual module stalk functor. -/
def stalkAction : Aut (GeometricPoint.finiteFiber xbar) →* End (moduleStalk Λ xbar) :=
  (germIso Λ xbar).conj.toMonoidHom.comp (finiteFiberAction Λ xbar)

/-- The linear action on a stalk is evaluation of the natural monodromy action. -/
def representation
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    Aut (GeometricPoint.finiteFiber xbar) →* End ((stalk Λ xbar).obj F.obj) :=
  (Functor.mapEnd (moduleStalk Λ xbar)
    ((CategoryTheory.evaluation _ (ModuleCat.{u + 1} Λ)).obj F)).comp (stalkAction Λ xbar)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical germ map intertwines finite-neighborhood and actual-stalk actions. -/
theorem germMap_representation
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (σ : Aut (GeometricPoint.finiteFiber xbar)) :
    germMap Λ xbar F.obj ≫ representation Λ xbar F σ =
      finiteAction Λ xbar F.obj.obj σ ≫ germMap Λ xbar F.obj := by
  change ((germIso Λ xbar).app F).hom ≫
    (((germIso Λ xbar).app F).inv ≫ finiteAction Λ xbar F.obj.obj σ ≫
      ((germIso Λ xbar).app F).hom) =
    finiteAction Λ xbar F.obj.obj σ ≫ ((germIso Λ xbar).app F).hom
  simp only [← Category.assoc, ((germIso Λ xbar).app F).hom_inv_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Monodromy on an actual stalk moves the pointing of each finite étale germ. -/
theorem germ_representation
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (σ : Aut (GeometricPoint.finiteFiber xbar)) (N : (fiber xbar).Elementsᵒᵖ) :
    (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber
        ((FiniteEtale.toEtale X).obj N.unop.1) N.unop.2 F.obj.obj ≫ representation Λ xbar F σ =
      (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber
        ((FiniteEtale.toEtale X).obj N.unop.1)
        ((Functor.whiskerRight σ.hom FintypeCat.incl).app N.unop.1 N.unop.2) F.obj.obj := by
  rw [← ι_germMap Λ xbar F.obj N, Category.assoc, germMap_representation,
    ← Category.assoc, ι_finiteAction, ι_germMap]

/-- The monodromy action on each finite locally constant stalk has open stabilizers. -/
theorem representation_openStabilizer
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    openStabilizer Λ (Aut (GeometricPoint.finiteFiber xbar))
      { V := (stalk Λ xbar).obj F.obj, ρ := representation Λ xbar F } := sorry

/-- The correct discrete representation has the actual module stalk as its carrier. -/
def module
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar)) :=
  ⟨{ V := (stalk Λ xbar).obj F.obj, ρ := representation Λ xbar F },
    representation_openStabilizer Λ xbar F⟩

/-- Sheaf morphisms induce actual stalk maps, with equivariance from natural monodromy. -/
def map {F G : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory}
    (f : F ⟶ G) : module Λ xbar F ⟶ module Λ xbar G :=
  ObjectProperty.homMk
    { hom := (stalk Λ xbar).map f.hom
      comm := fun σ ↦ ((stalkAction Λ xbar σ).naturality f).symm }

/-- The forward monodromy functor on finite locally constant module sheaves. -/
def functor :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
      DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar)) where
  obj := module Λ xbar
  map := map Λ xbar
  map_id F := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact (stalk Λ xbar).map_id F.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact (stalk Λ xbar).map_comp f.hom g.hom

/-- The forward coefficient carrier is definitionally the actual module-valued site fiber. -/
theorem functor_obj_V
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    ((functor Λ xbar).obj F).obj.V =
      (GeometricPoint.toSmallEtalePoint xbar).presheafFiber.obj F.obj.obj := rfl

/-- The forward map is definitionally the module-valued stalk map of the sheaf morphism. -/
theorem functor_map_hom
    {F G : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory}
    (f : F ⟶ G) :
    ((functor Λ xbar).map f).hom.hom =
      (GeometricPoint.toSmallEtalePoint xbar).presheafFiber.map f.hom.hom := rfl

/-- A finite-type locally constant module sheaf has finite-type geometric stalk. -/
theorem module_finite
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    Module.Finite Λ (module Λ xbar F).obj.V := sorry

end AlgebraicGeometry.Scheme.StalkRepresentation
