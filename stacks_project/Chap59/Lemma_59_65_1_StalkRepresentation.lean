module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap58.Theorem_58_6_2_Fiber

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

universe u

namespace AlgebraicGeometry.Scheme.StalkRepresentation

variable {X : Scheme.{u}} [ConnectedSpace X]
variable (Λ : Type (u + 1)) [Ring Λ]
variable (xbar : GeometricPoint X)

/-- The finite étale inclusion keeps the underlying étale object and morphism. -/
def finiteEtaleInclusion : FiniteEtale X ⥤ X.Etale where
  obj := finiteEtaleToEtale
  map := finiteEtaleToEtaleMap

/-- The set-valued finite étale fiber functor at the geometric point. -/
abbrev fiber : FiniteEtale X ⥤ Type u :=
  standardFiniteEtaleFiber xbar ⋙ FintypeCat.incl

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
abbrev move (σ : Aut (standardFiniteEtaleFiber xbar)) :
    (fiber xbar).Elements ⥤ (fiber xbar).Elements where
  obj N := ⟨N.1, (Functor.whiskerRight σ.hom FintypeCat.incl).app N.1 N.2⟩
  map {N K} f := ⟨f.val, by
    simpa using (NatTrans.naturality_apply
      (Functor.whiskerRight σ.hom FintypeCat.incl) f.val N.2).symm.trans
        (congrArg (fun y ↦ (Functor.whiskerRight σ.hom FintypeCat.incl).app K.1 y)
          f.property)⟩

/-- The colimit endomorphism induced by a natural automorphism of the finite fiber. -/
def finiteAction (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
    (σ : Aut (standardFiniteEtaleFiber xbar)) :
    colimit (diagram Λ xbar F) ⟶ colimit (diagram Λ xbar F) :=
  colimit.desc (diagram Λ xbar F)
    { pt := colimit (diagram Λ xbar F)
      ι :=
        { app N := colimit.ι (diagram Λ xbar F) (op ((move xbar σ).obj N.unop))
          naturality := fun N K f ↦
            colimit.w (diagram Λ xbar F) ((move xbar σ).map f.unop).op } }

/-- On a germ, the action moves its pointing and leaves its section unchanged. -/
theorem ι_finiteAction (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
    (σ : Aut (standardFiniteEtaleFiber xbar)) (N : (fiber xbar).Elementsᵒᵖ) :
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
    (σ τ : Aut (standardFiniteEtaleFiber xbar)) :
    finiteAction Λ xbar F (σ * τ) = finiteAction Λ xbar F τ ≫ finiteAction Λ xbar F σ := by
  apply colimit.hom_ext (F := diagram Λ xbar F)
  intro N
  rw [ι_finiteAction, ← Category.assoc, ι_finiteAction, ι_finiteAction]
  rfl

/-- The linear representation on the finite-neighborhood colimit. -/
def finiteRepresentation (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    Aut (standardFiniteEtaleFiber xbar) →* End (colimit (diagram Λ xbar F)) where
  toFun := finiteAction Λ xbar F
  map_one' := finiteAction_one Λ xbar F
  map_mul' := finiteAction_mul Λ xbar F

/-- The actual module stalk, obtained from the small étale site point. -/
def stalk : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
  sheafToPresheaf _ _ ⋙ (geometricPointEtalePoint xbar).presheafFiber

/-- The canonical germ cocone sends a pointed finite étale section into the actual stalk. -/
def germCocone (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Cocone (diagram Λ xbar F.obj) where
  pt := (stalk Λ xbar).obj F
  ι :=
    { app N := (geometricPointEtalePoint xbar).toPresheafFiber
        (finiteEtaleToEtale N.unop.1) N.unop.2 F.obj
      naturality := fun N K f ↦ by
        change F.obj.map (finiteEtaleToEtaleMap f.unop.val).op ≫
          (geometricPointEtalePoint xbar).toPresheafFiber _ K.unop.2 F.obj =
            (geometricPointEtalePoint xbar).toPresheafFiber _ N.unop.2 F.obj ≫ 𝟙 _
        rw [Category.comp_id, (geometricPointEtalePoint xbar).toPresheafFiber_w]
        exact congrArg (fun y ↦ (geometricPointEtalePoint xbar).toPresheafFiber _ y F.obj)
          f.unop.property }

/-- The specified finite-neighborhood-to-stalk map. -/
def germMap (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (finiteFiber Λ xbar).obj F.obj ⟶ (stalk Λ xbar).obj F :=
  colimit.desc (diagram Λ xbar F.obj) (germCocone Λ xbar F)

/-- The specified germ comparison restricts to the usual small-étale germ map. -/
theorem ι_germMap (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (N : (fiber xbar).Elementsᵒᵖ) :
    colimit.ι (diagram Λ xbar F.obj) N ≫ germMap Λ xbar F =
      (geometricPointEtalePoint xbar).toPresheafFiber
        (finiteEtaleToEtale N.unop.1) N.unop.2 F.obj :=
  colimit.ι_desc _ _

/-- The induced colimit map is the sheaf morphism on each finite étale germ. -/
theorem ι_finiteFiber_map {F G : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ} (f : F ⟶ G)
    (N : (fiber xbar).Elementsᵒᵖ) :
    colimit.ι (diagram Λ xbar F) N ≫ (finiteFiber Λ xbar).map f =
      f.app (op (finiteEtaleToEtale N.unop.1)) ≫ colimit.ι (diagram Λ xbar G) N :=
  colimit.ι_map _ _

set_option backward.isDefEq.respectTransparency false in
/-- Monodromy on finite-neighborhood fibers is natural in the module presheaf. -/
theorem finiteAction_naturality {F G : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ} (f : F ⟶ G)
    (σ : Aut (standardFiniteEtaleFiber xbar)) :
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
  exact ((geometricPointEtalePoint xbar).toPresheafFiber_naturality
    f.hom (finiteEtaleToEtale N.unop.1) N.unop.2).symm

variable [Finite Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- Finite étale neighborhoods compute the stalk of a finite locally constant module sheaf.
This is invertibility of the specified germ map, not equality of distinct colimit objects. -/
instance germMap_isIso
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    IsIso (germMap Λ xbar F.obj) := sorry

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
  NatIso.ofComponents (fun F ↦
    @asIso _ _ _ _ (germMap Λ xbar F.obj) (germMap_isIso Λ xbar F))
    (fun f ↦ germMap_naturality Λ xbar f.hom)

/-- Natural automorphisms of finite étale fibers act linearly and naturally on germ colimits. -/
def finiteFiberAction : Aut (standardFiniteEtaleFiber xbar) →* End (finiteModuleFiber Λ xbar) where
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
def stalkAction : Aut (standardFiniteEtaleFiber xbar) →* End (moduleStalk Λ xbar) :=
  (germIso Λ xbar).conj.toMonoidHom.comp (finiteFiberAction Λ xbar)

/-- The linear action on a stalk is evaluation of the natural monodromy action. -/
def representation
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    Aut (standardFiniteEtaleFiber xbar) →* End ((stalk Λ xbar).obj F.obj) :=
  (Functor.mapEnd (moduleStalk Λ xbar)
    ((CategoryTheory.evaluation _ (ModuleCat.{u + 1} Λ)).obj F)).comp (stalkAction Λ xbar)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical germ map intertwines finite-neighborhood and actual-stalk actions. -/
theorem germMap_representation
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (σ : Aut (standardFiniteEtaleFiber xbar)) :
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
    (σ : Aut (standardFiniteEtaleFiber xbar)) (N : (fiber xbar).Elementsᵒᵖ) :
    (geometricPointEtalePoint xbar).toPresheafFiber
        (finiteEtaleToEtale N.unop.1) N.unop.2 F.obj.obj ≫ representation Λ xbar F σ =
      (geometricPointEtalePoint xbar).toPresheafFiber
        (finiteEtaleToEtale N.unop.1)
        ((Functor.whiskerRight σ.hom FintypeCat.incl).app N.unop.1 N.unop.2) F.obj.obj := by
  rw [← ι_germMap Λ xbar F.obj N, Category.assoc, germMap_representation,
    ← Category.assoc, ι_finiteAction, ι_germMap]

/-- The monodromy action on each finite locally constant stalk has open stabilizers. -/
theorem representation_openStabilizer
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    openStabilizer Λ (Aut (standardFiniteEtaleFiber xbar))
      { V := (stalk Λ xbar).obj F.obj, ρ := representation Λ xbar F } := sorry

/-- The correct discrete representation has the actual module stalk as its carrier. -/
def module
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar)) :=
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
      DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar)) where
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
      (geometricPointEtalePoint xbar).presheafFiber.obj F.obj.obj := rfl

/-- The forward map is definitionally the module-valued stalk map of the sheaf morphism. -/
theorem functor_map_hom
    {F G : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory}
    (f : F ⟶ G) :
    ((functor Λ xbar).map f).hom.hom =
      (geometricPointEtalePoint xbar).presheafFiber.map f.hom.hom := rfl

/-- A finite-type locally constant module sheaf has finite-type geometric stalk. -/
theorem module_finite
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    Module.Finite Λ (module Λ xbar F).obj.V := sorry

end AlgebraicGeometry.Scheme.StalkRepresentation
