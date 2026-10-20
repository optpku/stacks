/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Skyscraper module presheaves and stalks

This file constructs the module-presheaf skyscraper at a point.  On an open containing the point,
its value is a stalk module restricted along the germ map; away from the point, its value is the
zero module.  This gives the module-valued refinement of the usual stalk-skyscraper adjunction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presheaf Opposite TopCat
  TopologicalSpace

noncomputable section

universe u

namespace PresheafOfModules.Skyscraper

variable {X : TopCat.{u}}

/-- The value on `U` of the skyscraper module presheaf attached to an `Oₓ`-module: restrict
scalars along `O(U) ⟶ Oₓ` when `x ∈ U`, and use the zero module otherwise. -/
@[stacks 007K "module-presheaf skyscraper value"]
noncomputable def obj (O : X.Presheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat (O.stalk x)) (U : (Opens X)ᵒᵖ) :
    ModuleCat ((ringPresheafOfComm O).obj U) :=
  @dite (ModuleCat ((ringPresheafOfComm O).obj U))
    (x ∈ U.unop) (Classical.dec _)
    (fun h => (ModuleCat.restrictScalars (O.germ U.unop x h).hom).obj N)
    (fun _ => ⊤_ ModuleCat.{u} ((ringPresheafOfComm O).obj U))

/-- On an open containing `x`, the skyscraper value is restriction of scalars along the germ
map. -/
theorem obj_eq_of_mem (O : X.Presheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat (O.stalk x)) (U : (Opens X)ᵒᵖ) (h : x ∈ U.unop) :
    obj O x N U =
      (ModuleCat.restrictScalars (O.germ U.unop x h).hom).obj N := sorry

/-- On an open not containing `x`, the skyscraper value is a zero module. -/
theorem obj_isZero_of_not_mem (O : X.Presheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat (O.stalk x)) (U : (Opens X)ᵒᵖ) (h : x ∉ U.unop) :
    IsZero (obj O x N U) := sorry

/-- Restriction followed by a germ is the germ from the larger open. -/
theorem germ_comp (O : X.Presheaf CommRingCat.{u}) (x : X)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (hV : x ∈ V.unop) :
    (O.germ U.unop x (f.unop.le hV)).hom =
      (O.germ V.unop x hV).hom.comp (O.map f).hom := sorry

/-- The restriction map of a skyscraper module presheaf.  On neighborhoods of `x` it is the
canonical comparison between two successive scalar restrictions; otherwise it is zero. -/
noncomputable def map (O : X.Presheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat (O.stalk x)) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    obj O x N U ⟶
      (ModuleCat.restrictScalars ((ringPresheafOfComm O).map f).hom).obj
        (obj O x N V) :=
  @dite (obj O x N U ⟶
      (ModuleCat.restrictScalars ((ringPresheafOfComm O).map f).hom).obj
        (obj O x N V))
    (x ∈ V.unop) (Classical.dec _)
    (fun hV =>
      let hU : x ∈ U.unop := f.unop.le hV
      eqToHom (dif_pos hU) ≫
        (ModuleCat.restrictScalarsComp'App
          (O.map f).hom (O.germ V.unop x hV).hom
          (O.germ U.unop x hU).hom
          (congrArg (fun k => k.hom) (O.germ_res' f x hV).symm :
            (O.germ U.unop x hU).hom =
              (O.germ V.unop x hV).hom.comp (O.map f).hom) N).hom ≫
        (ModuleCat.restrictScalars (O.map f).hom).map
          (eqToHom
            (dif_pos hV : obj O x N V =
              (ModuleCat.restrictScalars (O.germ V.unop x hV).hom).obj N).symm))
    (fun _ => 0)

/-- Skyscraper restriction maps preserve identities. -/
theorem map_id (O : X.Presheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat (O.stalk x)) (U : (Opens X)ᵒᵖ) :
    map O x N (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((ringPresheafOfComm O).map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom ((ringPresheafOfComm O).map_id U))).inv.app
          (obj O x N U) := sorry

/-- Skyscraper restriction maps preserve composition. -/
theorem map_comp (O : X.Presheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat (O.stalk x)) {U V W : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    map O x N (f ≫ g) =
      map O x N f ≫
        (ModuleCat.restrictScalars ((ringPresheafOfComm O).map f).hom).map
          (map O x N g) ≫
        (ModuleCat.restrictScalarsComp'
          ((ringPresheafOfComm O).map f).hom
          ((ringPresheafOfComm O).map g).hom
          ((ringPresheafOfComm O).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom
            ((ringPresheafOfComm O).map_comp f g))).inv.app (obj O x N W) := sorry

/-- The skyscraper presheaf of modules associated to an `Oₓ`-module. -/
@[stacks 007K "module-presheaf skyscraper"]
noncomputable def atPoint (O : X.Presheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat (O.stalk x)) : PresheafOfModules (ringPresheafOfComm O) where
  obj := obj O x N
  map := map O x N
  map_id := map_id O x N
  map_comp := map_comp O x N

/-- The component on `U` of the skyscraper morphism induced by a map of stalk modules. -/
noncomputable def mapApp (O : X.Presheaf CommRingCat.{u}) (x : X)
    {N N' : ModuleCat (O.stalk x)} (f : N ⟶ N') (U : (Opens X)ᵒᵖ) :
    obj O x N U ⟶ obj O x N' U :=
  @dite (obj O x N U ⟶ obj O x N' U)
    (x ∈ U.unop) (Classical.dec _)
    (fun h =>
      eqToHom (dif_pos h) ≫
        (ModuleCat.restrictScalars (O.germ U.unop x h).hom).map f ≫
        eqToHom
          (dif_pos h : obj O x N' U =
            (ModuleCat.restrictScalars (O.germ U.unop x h).hom).obj N').symm)
    (fun _ => 0)

/-- The components induced by a map of stalk modules commute with skyscraper restriction maps. -/
theorem mapApp_naturality (O : X.Presheaf CommRingCat.{u}) (x : X)
    {N N' : ModuleCat (O.stalk x)} (f : N ⟶ N')
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    map O x N i ≫
        (ModuleCat.restrictScalars ((ringPresheafOfComm O).map i).hom).map
          (mapApp O x f V) =
      mapApp O x f U ≫ map O x N' i := sorry

/-- A map of stalk modules induces a morphism of skyscraper module presheaves. -/
noncomputable def mapHom (O : X.Presheaf CommRingCat.{u}) (x : X)
    {N N' : ModuleCat (O.stalk x)} (f : N ⟶ N') :
    atPoint O x N ⟶ atPoint O x N' where
  app := mapApp O x f
  naturality := mapApp_naturality O x f

/-- Skyscraper sends identity maps of stalk modules to identity morphisms. -/
theorem mapHom_id (O : X.Presheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat (O.stalk x)) :
    mapHom O x (𝟙 N) = 𝟙 (atPoint O x N) := sorry

/-- Skyscraper sends composites of stalk-module maps to composites. -/
theorem mapHom_comp (O : X.Presheaf CommRingCat.{u}) (x : X)
    {N N' N'' : ModuleCat (O.stalk x)} (f : N ⟶ N') (g : N' ⟶ N'') :
    mapHom O x (f ≫ g) = mapHom O x f ≫ mapHom O x g := sorry

/-- The skyscraper functor from modules over `Oₓ` to presheaves of `O`-modules. -/
@[stacks 007K "module-presheaf skyscraper functor"]
noncomputable def functorOfCommRing (O : X.Presheaf CommRingCat.{u}) (x : X) :
    ModuleCat (O.stalk x) ⥤ PresheafOfModules (ringPresheafOfComm O) where
  obj := atPoint O x
  map := mapHom O x
  map_id := mapHom_id O x
  map_comp := mapHom_comp O x

namespace RestrictScalars

/-- Away from `x`, the two zero maps used in the scalar-change comparison compose to the
identity on the restricted skyscraper value. -/
theorem zero_hom_inv_id {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) (N : ModuleCat (O'.stalk x)) (U : (Opens X)ᵒᵖ) (h : x ∉ U.unop) :
    (0 : ((PresheafOfModules.restrictScalars (ringPresheafOfCommMap p)).obj
          (atPoint O' x N)).obj U ⟶
        (atPoint O x
          ((ModuleCat.restrictScalars
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)).obj N)).obj U) ≫
      0 =
        𝟙 (((PresheafOfModules.restrictScalars (ringPresheafOfCommMap p)).obj
          (atPoint O' x N)).obj U) := sorry

/-- Away from `x`, the two zero maps used in the scalar-change comparison compose to the
identity on the target skyscraper value. -/
theorem zero_inv_hom_id {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) (N : ModuleCat (O'.stalk x)) (U : (Opens X)ᵒᵖ) (h : x ∉ U.unop) :
    (0 : (atPoint O x
          ((ModuleCat.restrictScalars
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)).obj N)).obj U ⟶
        ((PresheafOfModules.restrictScalars (ringPresheafOfCommMap p)).obj
          (atPoint O' x N)).obj U) ≫
      0 =
        𝟙 ((atPoint O x
          ((ModuleCat.restrictScalars
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)).obj N)).obj U) := sorry

/-- Restricting a skyscraper along `O ⟶ O'`, evaluated on one open, agrees with restricting
its stalk module along `Oₓ ⟶ O'ₓ` and then forming the `O`-skyscraper. -/
@[stacks 007K "restriction of skyscraper module sections"]
noncomputable def appIso {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) (N : ModuleCat (O'.stalk x)) (U : (Opens X)ᵒᵖ) :
    ((PresheafOfModules.restrictScalars (ringPresheafOfCommMap p)).obj
      (atPoint O' x N)).obj U ≅
      (atPoint O x
        ((ModuleCat.restrictScalars
          (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)).obj N)).obj U :=
  @dite (_ ≅ _) (x ∈ U.unop) (Classical.dec _)
    (fun h =>
      eqToIso (congrArg
        (fun M : ModuleCat ((ringPresheafOfComm O').obj U) =>
          (ModuleCat.restrictScalars (p.app U).hom).obj M)
        (dif_pos h : obj O' x N U =
          (ModuleCat.restrictScalars (O'.germ U.unop x h).hom).obj N)) ≪≫
      (ModuleCat.restrictScalarsComp'App
        (p.app U).hom (O'.germ U.unop x h).hom
        ((O'.germ U.unop x h).hom.comp (p.app U).hom) rfl N).symm ≪≫
      (ModuleCat.restrictScalarsCongr
        (congrArg (fun k => k.hom)
          (TopCat.Presheaf.stalkFunctor_map_germ U.unop x h p).symm :
          (O'.germ U.unop x h).hom.comp (p.app U).hom =
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom).comp
              (O.germ U.unop x h).hom)).app N ≪≫
      ModuleCat.restrictScalarsComp'App
        (O.germ U.unop x h).hom
        (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)
        ((((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom).comp
          (O.germ U.unop x h).hom) rfl N ≪≫
      eqToIso
        (dif_pos h : obj O x
          ((ModuleCat.restrictScalars
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)).obj N) U =
          (ModuleCat.restrictScalars (O.germ U.unop x h).hom).obj
            ((ModuleCat.restrictScalars
              (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)).obj N)).symm)
    (fun h =>
      { hom := 0
        inv := 0
        hom_inv_id := zero_hom_inv_id p x N U h
        inv_hom_id := zero_inv_hom_id p x N U h })

/-- The sectionwise scalar-change isomorphisms for skyscrapers commute with restriction maps. -/
theorem appIso_naturality {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) (N : ModuleCat (O'.stalk x)) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    ((PresheafOfModules.restrictScalars (ringPresheafOfCommMap p)).obj
          (atPoint O' x N)).map f ≫
        (ModuleCat.restrictScalars ((ringPresheafOfComm O).map f).hom).map
          (appIso p x N V).hom =
      (appIso p x N U).hom ≫
        (atPoint O x
          ((ModuleCat.restrictScalars
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)).obj N)).map f := sorry

/-- Restriction of scalars commutes with the skyscraper construction on a fixed stalk module. -/
@[stacks 007K "restriction of a skyscraper module presheaf"]
noncomputable def objIso {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) (N : ModuleCat (O'.stalk x)) :
    (PresheafOfModules.restrictScalars (ringPresheafOfCommMap p)).obj
        (atPoint O' x N) ≅
      atPoint O x
        ((ModuleCat.restrictScalars
          (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)).obj N) :=
  PresheafOfModules.isoMk (appIso p x N)
    (fun _ _ f => appIso_naturality p x N f)

/-- The scalar-change isomorphism for skyscrapers is natural in the stalk module. -/
theorem objIso_naturality {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) {N N' : ModuleCat (O'.stalk x)} (f : N ⟶ N') :
    (PresheafOfModules.restrictScalars (ringPresheafOfCommMap p)).map
          (mapHom O' x f) ≫
        (objIso p x N').hom =
      (objIso p x N).hom ≫
        mapHom O x
          ((ModuleCat.restrictScalars
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)).map f) := sorry

/-- The inverse scalar-change comparison for skyscrapers is natural in the stalk module. -/
@[stacks 007K "inverse naturality of restriction for a skyscraper module presheaf"]
theorem objIso_inv_naturality {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) {N N' : ModuleCat (O'.stalk x)} (f : N ⟶ N') :
    mapHom O x
          ((ModuleCat.restrictScalars
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom)).map f) ≫
        (objIso p x N').inv =
      (objIso p x N).inv ≫
        (PresheafOfModules.restrictScalars (ringPresheafOfCommMap p)).map
          (mapHom O' x f) := sorry

/-- The forward skyscraper scalar-change comparisons form a natural transformation. -/
@[stacks 007K "forward skyscraper scalar-change natural transformation"]
noncomputable def functorNatTrans {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) :
    functorOfCommRing O' x ⋙
        PresheafOfModules.restrictScalars (ringPresheafOfCommMap p) ⟶
      ModuleCat.restrictScalars
          (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom) ⋙
        functorOfCommRing O x where
  app N := (objIso p x N).hom
  naturality _ _ f := objIso_naturality p x f

/-- The inverse skyscraper scalar-change comparisons form the inverse natural transformation. -/
@[stacks 007K "inverse skyscraper scalar-change natural transformation"]
noncomputable def functorInvNatTrans {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) :
    ModuleCat.restrictScalars
          (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom) ⋙
        functorOfCommRing O x ⟶
      functorOfCommRing O' x ⋙
        PresheafOfModules.restrictScalars (ringPresheafOfCommMap p) where
  app N := (objIso p x N).inv
  naturality _ _ f := objIso_inv_naturality p x f

/-- A component of the forward skyscraper scalar-change transformation is `objIso`. -/
@[simp, stacks 007K "forward skyscraper scalar-change natural transformation component"]
theorem functorNatTrans_app {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) (N : ModuleCat (O'.stalk x)) :
    (functorNatTrans p x).app N = (objIso p x N).hom := sorry

/-- A component of the inverse skyscraper scalar-change transformation is the inverse of
`objIso`. -/
@[simp, stacks 007K "inverse skyscraper scalar-change natural transformation component"]
theorem functorInvNatTrans_app {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) (N : ModuleCat (O'.stalk x)) :
    (functorInvNatTrans p x).app N = (objIso p x N).inv := sorry

/-- The forward skyscraper scalar-change transformation followed by its inverse is the identity. -/
@[simp, stacks 007K "skyscraper scalar-change natural transformation forward-inverse law"]
theorem functorNatTrans_hom_inv_id {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) :
    functorNatTrans p x ≫ functorInvNatTrans p x = 𝟙 _ := sorry

/-- The inverse skyscraper scalar-change transformation followed by its forward map is the
identity. -/
@[simp, stacks 007K "skyscraper scalar-change natural transformation inverse-forward law"]
theorem functorNatTrans_inv_hom_id {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) :
    functorInvNatTrans p x ≫ functorNatTrans p x = 𝟙 _ := sorry

/-- Restriction of scalars commutes naturally with the skyscraper functor. -/
@[stacks 007K "restriction commutes with the skyscraper functor"]
noncomputable def functorIso {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) :
    functorOfCommRing O' x ⋙
        PresheafOfModules.restrictScalars (ringPresheafOfCommMap p) ≅
      ModuleCat.restrictScalars
          (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p).hom) ⋙
        functorOfCommRing O x :=
  { hom := functorNatTrans p x
    inv := functorInvNatTrans p x
    hom_inv_id := functorNatTrans_hom_inv_id p x
    inv_hom_id := functorNatTrans_inv_hom_id p x }

/-- The forward natural transformation of `functorIso` is explicit. -/
@[simp, stacks 007K "skyscraper scalar-change natural isomorphism hom"]
theorem functorIso_hom {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O') (x : X) :
    (functorIso p x).hom = functorNatTrans p x := sorry

/-- The inverse natural transformation of `functorIso` is explicit. -/
@[simp, stacks 007K "skyscraper scalar-change natural isomorphism inverse"]
theorem functorIso_inv {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O') (x : X) :
    (functorIso p x).inv = functorInvNatTrans p x := sorry

/-- A component of `functorIso` is the objectwise skyscraper comparison. -/
@[simp, stacks 007K "skyscraper scalar-change natural isomorphism component"]
theorem functorIso_app {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) (N : ModuleCat (O'.stalk x)) :
    (functorIso p x).app N = objIso p x N := sorry

/-- The forward component of `functorIso` is the objectwise comparison map. -/
@[simp, stacks 007K "skyscraper scalar-change natural isomorphism hom component"]
theorem functorIso_hom_app {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) (N : ModuleCat (O'.stalk x)) :
    (functorIso p x).hom.app N = (objIso p x N).hom := sorry

/-- The inverse component of `functorIso` is the objectwise inverse comparison map. -/
@[simp, stacks 007K "skyscraper scalar-change natural isomorphism inverse component"]
theorem functorIso_inv_app {O O' : X.Presheaf CommRingCat.{u}} (p : O ⟶ O')
    (x : X) (N : ModuleCat (O'.stalk x)) :
    (functorIso p x).inv.app N = (objIso p x N).inv := sorry

end RestrictScalars

/-- The component of the adjunction map from a module presheaf to a skyscraper.  On a
neighborhood it is the germ map followed by the given map of stalk modules, and away from the
point it is zero. -/
noncomputable def toApp (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (f : PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ N)
    (U : (Opens X)ᵒᵖ) : F.obj U ⟶ obj O x N U :=
  @dite (F.obj U ⟶ obj O x N U) (x ∈ U.unop) (Classical.dec _)
    (fun h =>
      PresheafOfModules.germToStalk F x U.unop h ≫
        (ModuleCat.restrictScalars (O.germ U.unop x h).hom).map f ≫
        eqToHom
          (dif_pos h : obj O x N U =
            (ModuleCat.restrictScalars (O.germ U.unop x h).hom).obj N).symm)
    (fun _ => 0)

/-- On a neighborhood of `x`, `toApp` is the germ map followed by the given stalk-module map. -/
theorem toApp_of_mem (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (f : PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ N)
    (U : (Opens X)ᵒᵖ) (h : x ∈ U.unop) :
    toApp O x f U =
      PresheafOfModules.germToStalk F x U.unop h ≫
        (ModuleCat.restrictScalars (O.germ U.unop x h).hom).map f ≫
        eqToHom (obj_eq_of_mem O x N U h).symm := sorry

/-- The components of the map to a skyscraper commute with restriction. -/
theorem toApp_naturality (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (f : PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ N)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    F.map i ≫
        (ModuleCat.restrictScalars ((ringPresheafOfComm O).map i).hom).map
          (toApp O x f V) =
      toApp O x f U ≫ map O x N i := sorry

/-- A map from a module-presheaf stalk to `N` induces a map of the presheaf into the skyscraper
of `N`. -/
noncomputable def toHom (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (f : PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ N) :
    F ⟶ atPoint O x N where
  app := toApp O x f
  naturality := toApp_naturality O x f

/-- The neighborhood leg associated to a map into a skyscraper, with codomain the underlying
additive group of its stalk-module value. -/
noncomputable def leg (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (g : F ⟶ atPoint O x N) (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ F.presheaf).obj U) ⟶
      (forget₂ (ModuleCat (O.stalk x)) AddCommGrpCat.{u}).obj N :=
  (forget₂
      (ModuleCat ((ringPresheafOfComm O).obj
        ((OpenNhds.inclusion x).op.obj U))) AddCommGrpCat.{u}).map
    (g.app ((OpenNhds.inclusion x).op.obj U) ≫
      eqToHom (dif_pos U.unop.2))

/-- The neighborhood legs associated to a map into a skyscraper are compatible with
restriction. -/
theorem leg_naturality (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (g : F ⟶ atPoint O x N) {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ F.presheaf).map i) ≫ leg O x g V =
      leg O x g U := sorry

/-- The cocone from the neighborhood diagram of `F` to the value of a skyscraper. -/
noncomputable def cocone (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (g : F ⟶ atPoint O x N) : Cocone ((OpenNhds.inclusion x).op ⋙ F.presheaf) where
  pt := (forget₂ (ModuleCat (O.stalk x)) AddCommGrpCat.{u}).obj N
  ι :=
    { app := leg O x g
      naturality := fun _ _ i => leg_naturality O x g i }

/-- The additive map out of the stalk induced by a morphism into a skyscraper. -/
noncomputable def addMap (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (g : F ⟶ atPoint O x N) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.presheaf x ⟶
      (forget₂ (ModuleCat (O.stalk x)) AddCommGrpCat.{u}).obj N :=
  colimit.desc _ (cocone O x g)

/-- The additive map induced by `g` sends a germ to the corresponding neighborhood component of
`g`. -/
theorem addMap_germ (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (g : F ⟶ atPoint O x N) (U : Opens X) (h : x ∈ U) (m : F.obj (op U)) :
    addMap O x g (TopCat.Presheaf.germ F.presheaf U x h m) =
      eqToHom (obj_eq_of_mem O x N (op U) h) (g.app (op U) m) := sorry

/-- The additive map induced by a morphism into a skyscraper is linear over `Oₓ`. -/
theorem addMap_smul (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (g : F ⟶ atPoint O x N) (r : O.stalk x)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.presheaf x) :
    addMap O x g (r • m) =
      HSMul.hSMul (α := O.stalk x) (β := N) r (addMap O x g m) := sorry

/-- A map from `F` into the skyscraper of `N` induces a linear map `Fₓ ⟶ N`. -/
noncomputable def fromHom (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (g : F ⟶ atPoint O x N) :
    PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ N :=
  ModuleCat.ofHom
    { toFun := addMap O x g
      map_add' := (addMap O x g).hom.map_add
      map_smul' := addMap_smul O x g }

/-- Passing from a stalk map to a skyscraper map and back recovers the stalk map. -/
theorem from_to (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (f : PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ N) :
    fromHom O x (toHom O x f) = f := sorry

/-- Passing from a skyscraper map to a stalk map and back recovers the skyscraper map. -/
theorem to_from (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (g : F ⟶ atPoint O x N) :
    toHom O x (fromHom O x g) = g := sorry

/-- Maps from the stalk of `F` to `N` are equivalent to maps from `F` to the skyscraper of
`N`. -/
@[stacks 007K "module-presheaf stalk-skyscraper Hom equivalence"]
noncomputable def homEquiv (O : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (ringPresheafOfComm O)) (N : ModuleCat (O.stalk x)) :
    (PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ N) ≃
      (F ⟶ atPoint O x N) where
  toFun := toHom O x
  invFun := fromHom O x
  left_inv := from_to O x
  right_inv := to_from O x

/-- The inverse stalk-skyscraper Hom equivalence is natural in the module presheaf. -/
theorem homEquiv_naturality_left_symm (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F G : PresheafOfModules (ringPresheafOfComm O)} {N : ModuleCat (O.stalk x)}
    (f : F ⟶ G) (g : G ⟶ atPoint O x N) :
    (homEquiv O x F N).symm (f ≫ g) =
      PresheafOfModules.stalkMapOfCommRing f x ≫
        (homEquiv O x G N).symm g := sorry

/-- The stalk-skyscraper Hom equivalence is natural in the stalk module. -/
theorem homEquiv_naturality_right (O : X.Presheaf CommRingCat.{u}) (x : X)
    {F : PresheafOfModules (ringPresheafOfComm O)} {N N' : ModuleCat (O.stalk x)}
    (f : PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ N) (g : N ⟶ N') :
    homEquiv O x F N' (f ≫ g) =
      homEquiv O x F N f ≫ mapHom O x g := sorry

/-- The stalk functor for module presheaves over a commutative-ring presheaf is left adjoint to
the skyscraper functor. -/
@[stacks 007K "module-presheaf stalk-skyscraper adjunction"]
noncomputable def adjunctionOfCommRing (O : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.stalkFunctorOfCommRing O x ⊣ functorOfCommRing O x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv O x
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm O x
      homEquiv_naturality_right := homEquiv_naturality_right O x }

end PresheafOfModules.Skyscraper
