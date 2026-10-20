/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Simplicial
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Assembly and evaluation of module sheaves on the simplicial site -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

-- Private implementation maps occur in the bodies of exposed public constructions.
set_option backward.privateInPublic true

universe u

namespace CategoryTheory.SimplicialSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [GrothendieckTopology.HasSheafCompose (topology J)
    (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Restriction maps for a degreewise family of modules over a simplicial ring sheaf, as maps of
modules on the simplicial site. -/
private def ofDegreewiseAddMap (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) :
    (forget₂ (_root_.ModuleCat _) AddCommGrpCat).obj
        ((objFamily (op X.unop.1)).val.obj (op X.unop.2)) ⟶
      (forget₂ (_root_.ModuleCat _) AddCommGrpCat).obj
        ((ModuleCat.restrictScalars
          ((CategoryTheory.Sheaf.ringSheafOfComm (ringSheaf 𝒪)).obj.map f).hom).obj
          ((objFamily (op Y.unop.1)).val.obj (op Y.unop.2))) :=
  AddCommGrpCat.ofHom
    (((mapFamily (op X.unop.1) (op Y.unop.1) f.unop.1.op).val.app
        (op Y.unop.2)).hom.toAddMonoidHom.comp
      ((objFamily (op X.unop.1)).val.map f.unop.2.op).hom.toAddMonoidHom)

/-- The assembled section maps commute with scalar multiplication. -/
theorem ofDegreewiseMap_laws (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) :
    ∀ r, ofDegreewiseAddMap 𝒪 objFamily mapFamily f ≫
        ((ModuleCat.restrictScalars
          ((CategoryTheory.Sheaf.ringSheafOfComm (ringSheaf 𝒪)).obj.map f).hom).obj
          ((objFamily (op Y.unop.1)).val.obj (op Y.unop.2))).smul r =
      ((objFamily (op X.unop.1)).val.obj (op X.unop.2)).smul r ≫
        ofDegreewiseAddMap 𝒪 objFamily mapFamily f :=
  sorry

/-- Restriction maps obtained from a degreewise family of module sheaves. -/
def ofDegreewiseMap (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) :
    (objFamily (op X.unop.1)).val.obj (op X.unop.2) ⟶
      (ModuleCat.restrictScalars
        ((CategoryTheory.Sheaf.ringSheafOfComm (SimplicialSite.ringSheaf 𝒪)).obj.map f).hom).obj
        ((objFamily (op Y.unop.1)).val.obj (op Y.unop.2)) :=
  ModuleCat.homMk (ofDegreewiseAddMap 𝒪 objFamily mapFamily f)
    (ofDegreewiseMap_laws 𝒪 objFamily mapFamily f)

/-- Composition coherence of the assembled transition maps, kept as an explicit
predicate so specializing it does not expose private simplex-code implementation terms. -/
@[irreducible] def degreewiseMapComp (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m)) : Prop :=
  ∀ {X Y Z : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)),
    (ofDegreewiseMap 𝒪 objFamily mapFamily (f ≫ g)).hom x =
      (ofDegreewiseMap 𝒪 objFamily mapFamily g).hom
        ((ofDegreewiseMap 𝒪 objFamily mapFamily f).hom x)

/-- Apply the composition-coherence predicate to specified composable site arrows. -/
theorem degreewiseMapComp_apply (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    (h : degreewiseMapComp 𝒪 objFamily mapFamily)
    {X Y Z : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)) :
    (ofDegreewiseMap 𝒪 objFamily mapFamily (f ≫ g)).hom x =
      (ofDegreewiseMap 𝒪 objFamily mapFamily g).hom
        ((ofDegreewiseMap 𝒪 objFamily mapFamily f).hom x) := by
  unfold degreewiseMapComp at h
  exact h f g x

/-- Assemble a coherent degreewise family into a module on the simplicial site.
Identity and composition must hold for the actual assembled maps. -/
private def ofDegreewisePresheaf (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    (hId : ∀ (X : (SimplexCategory × C)ᵒᵖ)
      (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)),
      (ofDegreewiseMap 𝒪 objFamily mapFamily (𝟙 X)).hom x = x)
    (hComp : degreewiseMapComp 𝒪 objFamily mapFamily) :
    PresheafOfModules (CategoryTheory.Sheaf.ringSheafOfComm (ringSheaf 𝒪)).obj :=
    { obj := fun X ↦ (objFamily (op X.unop.1)).val.obj (op X.unop.2)
      map := fun f ↦ ofDegreewiseMap 𝒪 objFamily mapFamily f
      map_id := by
        intro X
        ext x
        exact hId X x
      map_comp := by
        intro X Y Z f g
        ext x
        exact degreewiseMapComp_apply 𝒪 objFamily mapFamily hComp f g x }

/-- A coherent degreewise family satisfies the sheaf condition on the simplicial site. -/
theorem ofDegreewise_isSheaf (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    (hId : ∀ (X : (SimplexCategory × C)ᵒᵖ)
      (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)),
      (ofDegreewiseMap 𝒪 objFamily mapFamily (𝟙 X)).hom x = x)
    (hComp : degreewiseMapComp 𝒪 objFamily mapFamily) :
    Presheaf.IsSheaf (topology J)
      (ofDegreewisePresheaf 𝒪 objFamily mapFamily hId hComp).presheaf :=
  sorry

/-- Assemble a coherent degreewise family into a module sheaf on the simplicial site. -/
def ofDegreewise (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    (hId : ∀ (X : (SimplexCategory × C)ᵒᵖ)
      (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)),
      (ofDegreewiseMap 𝒪 objFamily mapFamily (𝟙 X)).hom x = x)
    (hComp : degreewiseMapComp 𝒪 objFamily mapFamily) :
    ModuleCat.{u, u, u, u} (J := J) 𝒪 where
  val := ofDegreewisePresheaf 𝒪 objFamily mapFamily hId hComp
  isSheaf := ofDegreewise_isSheaf 𝒪 objFamily mapFamily hId hComp

/-- An assembled coherent module has the specified degreewise objects. -/
theorem ofDegreewise_obj (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    (hId : ∀ (X : (SimplexCategory × C)ᵒᵖ)
      (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)),
      (ofDegreewiseMap 𝒪 objFamily mapFamily (𝟙 X)).hom x = x)
    (hComp : degreewiseMapComp 𝒪 objFamily mapFamily)
    (X : (SimplexCategory × C)ᵒᵖ) :
    (ofDegreewise 𝒪 objFamily mapFamily hId hComp).val.obj X =
      (objFamily (op X.unop.1)).val.obj (op X.unop.2) := rfl

/-- An assembled coherent module has the specified transition maps. -/
theorem ofDegreewise_map (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    (hId : ∀ (X : (SimplexCategory × C)ᵒᵖ)
      (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)),
      (ofDegreewiseMap 𝒪 objFamily mapFamily (𝟙 X)).hom x = x)
    (hComp : degreewiseMapComp 𝒪 objFamily mapFamily)
    {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) :
    (ofDegreewise 𝒪 objFamily mapFamily hId hComp).val.map f =
      ofDegreewiseMap 𝒪 objFamily mapFamily f := rfl

/-- A compatible component family between already assembled modules defines a morphism.
The domain and codomain already contain their identity/composition laws. -/
def ofDegreewiseHom (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (M N : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) 𝒪)
    (α : ∀ X : (SimplexCategory × C)ᵒᵖ, M.val.obj X ⟶ N.val.obj X)
    (hα : ∀ {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X),
      (α Y).hom ((M.val.map f).hom x) = (N.val.map f).hom ((α X).hom x)) : M ⟶ N where
  val :=
    { app := α
      naturality := by
        intro X Y f
        ext x
        exact hα f x }

/-- The coherent assembled morphism has exactly the specified components. -/
theorem ofDegreewiseHom_app (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (M N : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) 𝒪)
    (α : ∀ X : (SimplexCategory × C)ᵒᵖ, M.val.obj X ⟶ N.val.obj X)
    (hα : ∀ {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X),
      (α Y).hom ((M.val.map f).hom x) = (N.val.map f).hom ((α X).hom x))
    (X : (SimplexCategory × C)ᵒᵖ) :
    (ofDegreewiseHom 𝒪 M N α hα).val.app X = α X := rfl


/-- The opposite product morphism keeping the simplicial degree fixed. -/
private def degreeSliceHom (n : SimplexCategoryᵒᵖ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    op (n.unop, U.unop) ⟶ op (n.unop, V.unop) :=
  Quiver.Hom.op (⟨𝟙 n.unop, f.unop⟩ : (n.unop, V.unop) ⟶ (n.unop, U.unop))

/-- The opposite product morphism keeping the site object fixed. -/
private def simplexSliceHom {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (U : Cᵒᵖ) :
    op (n.unop, U.unop) ⟶ op (m.unop, U.unop) :=
  Quiver.Hom.op (⟨f.unop, 𝟙 U.unop⟩ : (m.unop, U.unop) ⟶ (n.unop, U.unop))

private def evalAtDegreeAddMap
    {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) (n : SimplexCategoryᵒᵖ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    AddCommGrpCat.of (X.val.obj (op (n.unop, U.unop))) ⟶
      AddCommGrpCat.of (X.val.obj (op (n.unop, V.unop))) :=
  AddCommGrpCat.ofHom (X.val.map (degreeSliceHom n f)).hom.toAddMonoidHom

private def evalAtDegreeScalarLaw
    {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) (n : SimplexCategoryᵒᵖ) : Prop :=
  ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (r : (Sheaf.ringSheafOfComm (𝒪.obj n)).obj.obj U),
    evalAtDegreeAddMap X n f ≫
        ((_root_.ModuleCat.restrictScalars
          ((Sheaf.ringSheafOfComm (𝒪.obj n)).obj.map f).hom).obj
          (X.val.obj (op (n.unop, V.unop)))).smul r =
      (X.val.obj (op (n.unop, U.unop))).smul r ≫ evalAtDegreeAddMap X n f

private def evalAtDegreePresheaf
    {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) (n : SimplexCategoryᵒᵖ)
    (hScalar : evalAtDegreeScalarLaw X n) :
    PresheafOfModules (Sheaf.ringSheafOfComm (𝒪.obj n)).obj where
  obj U := X.val.obj (op (n.unop, U.unop))
  map f := _root_.ModuleCat.homMk (evalAtDegreeAddMap X n f) (hScalar f)
  map_id U := by
    ext t
    change (X.val.map (degreeSliceHom n (𝟙 U))).hom t = t
    have h : degreeSliceHom (C := C) n (𝟙 U) = 𝟙 _ := rfl
    rw [h, X.val.map_id]
    rfl
  map_comp f g := by
    ext t
    change (X.val.map (degreeSliceHom n (f ≫ g))).hom t =
      (X.val.map (degreeSliceHom n g)).hom ((X.val.map (degreeSliceHom n f)).hom t)
    have h : degreeSliceHom n (f ≫ g) = degreeSliceHom n f ≫ degreeSliceHom n g := by
      apply Quiver.Hom.unop_inj
      apply Prod.ext <;> simp [degreeSliceHom]
    rw [h]
    exact X.val.map_comp_apply _ _ _

/-- Fixed-degree evaluation has compatible scalar actions and satisfies the sheaf condition. -/
theorem evalAtDegree_laws {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) (n : SimplexCategoryᵒᵖ) :
    evalAtDegreeScalarLaw X n ∧
      ∀ hScalar, Presheaf.IsSheaf J (evalAtDegreePresheaf X n hScalar).presheaf :=
  sorry

/-- Evaluation of a module sheaf at a fixed simplicial degree. -/
def evalAtDegree {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) (n : SimplexCategoryᵒᵖ) :
    ringedSiteModuleCategory J (𝒪.obj n) where
  val := evalAtDegreePresheaf X n (evalAtDegree_laws X n).1
  isSheaf := (evalAtDegree_laws X n).2 _

/-- Degree evaluation has the original sections at that degree. -/
theorem evalAtDegree_obj {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (evalAtDegree X n).val.obj U = X.val.obj (op (n.unop, U.unop)) :=
  rfl

/-- Degree evaluation of a morphism commutes with site restriction. -/
theorem evalAtDegreeHom_naturality
    {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    {X Y : ModuleCat.{u, u, u, u} (J := J) 𝒪} (α : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (evalAtDegree X n).val.map f ≫
        (_root_.ModuleCat.restrictScalars _).map (α.val.app (op (n.unop, V.unop))) =
      α.val.app (op (n.unop, U.unop)) ≫ (evalAtDegree Y n).val.map f :=
  sorry

/-- Evaluation of a module morphism at a fixed simplicial degree. -/
def evalAtDegreeHom {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    {X Y : ModuleCat.{u, u, u, u} (J := J) 𝒪} (α : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    evalAtDegree X n ⟶ evalAtDegree Y n where
  val :=
    { app := fun U ↦ α.val.app (op (n.unop, U.unop))
      naturality := evalAtDegreeHom_naturality α n }

private def evalAtDegreeMapAddComponent
    {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (U : Cᵒᵖ) :
    AddCommGrpCat.of ((evalAtDegree X n).val.obj U) ⟶
      AddCommGrpCat.of (((restrictionAlong (𝒪.map f)).obj (evalAtDegree X m)).val.obj U) :=
  AddCommGrpCat.ofHom (X.val.map (simplexSliceHom f U)).hom.toAddMonoidHom

private def evalAtDegreeMapScalarLaw
    {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) : Prop :=
  ∀ U r, evalAtDegreeMapAddComponent X f U ≫
        (((restrictionAlong (𝒪.map f)).obj (evalAtDegree X m)).val.obj U).smul r =
      ((evalAtDegree X n).val.obj U).smul r ≫ evalAtDegreeMapAddComponent X f U

private def evalAtDegreeMapComponent
    {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (hScalar : evalAtDegreeMapScalarLaw X f) (U : Cᵒᵖ) :
    (evalAtDegree X n).val.obj U ⟶
      ((restrictionAlong (𝒪.map f)).obj (evalAtDegree X m)).val.obj U :=
  _root_.ModuleCat.homMk (evalAtDegreeMapAddComponent X f U) (hScalar U)

/-- Simplicial transitions are scalar compatible and commute with site restriction. -/
theorem evalAtDegreeMap_laws
    {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    evalAtDegreeMapScalarLaw X f ∧
      ∀ hScalar {U V : Cᵒᵖ} (g : U ⟶ V),
      (evalAtDegree X n).val.map g ≫
          (_root_.ModuleCat.restrictScalars _).map (evalAtDegreeMapComponent X f hScalar V) =
        evalAtDegreeMapComponent X f hScalar U ≫
          ((restrictionAlong (𝒪.map f)).obj (evalAtDegree X m)).val.map g :=
  sorry

/-- A simplicial operator induces a map of degree evaluations after scalar restriction. -/
def evalAtDegreeMap {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : ModuleCat.{u, u, u, u} (J := J) 𝒪) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    evalAtDegree X n ⟶ (restrictionAlong (𝒪.map f)).obj (evalAtDegree X m) where
  val :=
    { app := evalAtDegreeMapComponent X f (evalAtDegreeMap_laws X f).1
      naturality := (evalAtDegreeMap_laws X f).2 _ }

section ConstantCoefficients

variable (B : Sheaf J CommRingCat.{u})

private def constantModuleDiagramTransition
    (X : ModuleCat.{u, u, u, u} (J := J) ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B))
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    evalAtDegree X n ⟶ evalAtDegree X m :=
  evalAtDegreeMap X f ≫
    (SheafOfModules.Restriction.idComponentIso'
      (SheafOfModules.RingedSite.ringSheafMap (𝟙 B))
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map_id B)
      (evalAtDegree X m)).inv

/-- Constant-coefficient degree evaluation respects identities, composition, and module maps. -/
theorem constantModuleDiagram_laws :
    (∀ (X : ModuleCat.{u, u, u, u} (J := J)
        ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B))
      (n : SimplexCategoryᵒᵖ), constantModuleDiagramTransition B X (𝟙 n) = 𝟙 _) ∧
    (∀ (X : ModuleCat.{u, u, u, u} (J := J)
        ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B))
      {n m k : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ k),
      constantModuleDiagramTransition B X (f ≫ g) =
        constantModuleDiagramTransition B X (n := n) (m := m) f ≫
          constantModuleDiagramTransition B X (n := m) (m := k) g) ∧
    (∀ {X Y : ModuleCat.{u, u, u, u} (J := J)
        ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B)} (α : X ⟶ Y)
      {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m),
      evalAtDegreeHom α n ≫ constantModuleDiagramTransition B Y (n := n) (m := m) f =
        constantModuleDiagramTransition B X (n := n) (m := m) f ≫ evalAtDegreeHom α m) :=
  sorry

/-- A module sheaf with constant simplicial coefficients gives a simplicial diagram of modules. -/
def constantModuleDiagram :
    ModuleCat.{u, u, u, u} (J := J) ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B) ⥤
      (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) where
  obj X :=
    { obj := evalAtDegree X
      map := constantModuleDiagramTransition B X
      map_id := (constantModuleDiagram_laws B).1 X
      map_comp := (constantModuleDiagram_laws B).2.1 X }
  map {X Y} α :=
    { app := fun n => evalAtDegreeHom
        (𝒪 := (SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B)
        (X := X) (Y := Y) α n
      naturality := fun {n m} f =>
        ((constantModuleDiagram_laws B).2.2 (X := X) (Y := Y) α (n := n) (m := m) f).symm }
  map_id X := by
    ext n U t
    rfl
  map_comp α β := rfl

/-- Constant-coefficient degree evaluation is additive. -/
instance constantModuleDiagram_additive : (constantModuleDiagram B).Additive :=
  sorry

variable [UnivLE.{u, u}] [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify (topology J) AddCommGrpCat.{u}]
variable [GrothendieckTopology.WEqualsLocallyBijective (topology J) AddCommGrpCat.{u}]

/-- Constant-coefficient degree evaluation preserves finite limits. -/
instance constantModuleDiagram_preservesFiniteLimits :
    PreservesFiniteLimits (constantModuleDiagram B) :=
  sorry

/-- Constant-coefficient degree evaluation preserves finite colimits. -/
instance constantModuleDiagram_preservesFiniteColimits :
    PreservesFiniteColimits (constantModuleDiagram B) :=
  sorry

variable [HasDerivedCategory
    (ModuleCat.{u, u, u, u} (J := J) ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B))]
variable [HasDerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B)]

/-- The exact degree-evaluation functor induced on unbounded derived categories. -/
def constantModuleDiagramDerived :=
  (constantModuleDiagram B).mapDerivedCategory

/-- Derived degree evaluation of a single module is its degreewise single diagram. -/
def constantModuleDiagramSingleIso :=
  (constantModuleDiagram B).mapDerivedCategorySingleFunctor 0

end ConstantCoefficients

end CategoryTheory.SimplicialSite
