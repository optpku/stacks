/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Modules.PullbackSections

variable {S : Scheme.{u}}

/-- The restriction map on global sections of pullback modules along a morphism of schemes over
`S`. -/
noncomputable def map (ℱ : S.Modules) {A B : Over S} (φ : A ⟶ B) :
    Scheme.Modules.globalSections ((Scheme.Modules.pullback B.hom).obj ℱ) ⟶
      Scheme.Modules.globalSections ((Scheme.Modules.pullback A.hom).obj ℱ) :=
  let h := congrArg
    (fun f : A.left ⟶ S ↦
      Scheme.Modules.globalSections ((Scheme.Modules.pullback f).obj ℱ))
    (Over.w φ)
  Scheme.Modules.globalSectionsPullbackComp φ.left B.hom ℱ ≫ eqToHom h

/-- The restriction map on pullback-module global sections is the identity on an identity
morphism over `S`. -/
theorem map_id (ℱ : S.Modules) (A : Over S) : map ℱ (𝟙 A) = 𝟙 _ := sorry

/-- Restriction maps on pullback-module global sections respect composition over `S`. -/
theorem map_comp (ℱ : S.Modules) {A B C : Over S} (φ : A ⟶ B) (ψ : B ⟶ C) :
    map ℱ (φ ≫ ψ) = map ℱ ψ ≫ map ℱ φ := sorry

/-- The presheaf on schemes over `S` sending `f : T ⟶ S` to the additive group of global
sections of `f^*ℱ`. -/
noncomputable def over (S : Scheme.{u}) (ℱ : S.Modules) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj A := Scheme.Modules.globalSections
    ((Scheme.Modules.pullback A.unop.hom).obj ℱ)
  map φ := map ℱ φ.unop
  map_id A := map_id ℱ A.unop
  map_comp φ ψ := map_comp ℱ ψ.unop φ.unop

/-- The value of `over S ℱ` at `f : T ⟶ S` is the global sections of `f^*ℱ`. -/
theorem over_obj (S : Scheme.{u}) (ℱ : S.Modules) (A : Over S) :
    (over S ℱ).obj (op A) =
      Scheme.Modules.globalSections ((Scheme.Modules.pullback A.hom).obj ℱ) := sorry

/-- The action of `over S ℱ` on a morphism over `S` is the corresponding restriction map. -/
theorem over_map (S : Scheme.{u}) (ℱ : S.Modules) {A B : Over S} (φ : A ⟶ B) :
    (over S ℱ).map φ.op = map ℱ φ := sorry

section ModulePresheaf

variable {C : Type w} [Category.{v} C]

/-- Global sections of the pullback of a scheme module along an object of a
category over the base, with their natural module structure. -/
noncomputable abbrev moduleObj
    (p : C ⥤ Over S) (ℱ : S.Modules) (U : Cᵒᵖ) :
    ModuleCat.{u} ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).obj U) :=
  RingedSpace.moduleGlobalSectionsFunctor
    (p.obj U.unop).left.toRingedSpace |>.obj
      ((Scheme.Modules.pullback (p.obj U.unop).hom).obj ℱ)

/-- Pullback of module sections is semilinear for pullback of global functions. -/
theorem moduleMap_smul
    (p : C ⥤ Over S) (ℱ : S.Modules) {U V : Cᵒᵖ} (f : U ⟶ V)
    (r : (Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).obj U)
    (s : moduleObj p ℱ U) :
    (map ℱ (p.map f.unop)).hom (r • s) =
      @SMul.smul ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).obj V)
        (moduleObj p ℱ V) (ModuleCat.isModule (moduleObj p ℱ V)).toSMul
        ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map f r)
        ((map ℱ (p.map f.unop)).hom s) := sorry

/-- The semilinear restriction map on global sections of pullback modules. -/
noncomputable def moduleMap
    (p : C ⥤ Over S) (ℱ : S.Modules) {U V : Cᵒᵖ} (f : U ⟶ V) :
    moduleObj p ℱ U ⟶
      (ModuleCat.restrictScalars
        ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map f).hom).obj
          (moduleObj p ℱ V) :=
  let source := moduleObj p ℱ U
  let target :=
    (ModuleCat.restrictScalars
      ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map f).hom).obj
        (moduleObj p ℱ V)
  @ModuleCat.ofHom ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).obj U) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := (map ℱ (p.map f.unop)).hom
      map_add' := (map ℱ (p.map f.unop)).hom.map_add
      map_smul' := moduleMap_smul p ℱ f }

/-- The pullback-sections restriction map on an identity is the canonical
identity map with restricted scalars. -/
theorem moduleMap_id (p : C ⥤ Over S) (ℱ : S.Modules) (U : Cᵒᵖ) :
    moduleMap p ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom
          ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map_id U))).inv.app _ := sorry

/-- Pullback-sections restriction maps respect composition. -/
theorem moduleMap_comp
    (p : C ⥤ Over S) (ℱ : S.Modules)
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    moduleMap p ℱ (f ≫ g) =
      moduleMap p ℱ f ≫
        (ModuleCat.restrictScalars
          ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map f).hom).map
            (moduleMap p ℱ g) ≫
        (ModuleCat.restrictScalarsComp'
          ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map f).hom
          ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map g).hom
          ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom
            ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map_comp f g))).inv.app _ := sorry

/-- The presheaf of modules whose value at `f : T ⟶ S` is `Γ(T, f^*ℱ)`. -/
noncomputable def modulePresheaf (p : C ⥤ Over S) (ℱ : S.Modules) :
    _root_.PresheafOfModules (Scheme.Site.structurePresheaf (p ⋙ Over.forget S)) where
  obj U := moduleObj p ℱ U
  map f := moduleMap p ℱ f
  map_id U := moduleMap_id p ℱ U
  map_comp f g := moduleMap_comp p ℱ f g

/-- Objectwise, `modulePresheaf p ℱ` is the module of global sections of the
corresponding pullback of `ℱ`. -/
theorem modulePresheaf_obj (p : C ⥤ Over S) (ℱ : S.Modules) (U : Cᵒᵖ) :
    (modulePresheaf p ℱ).obj U = moduleObj p ℱ U := sorry

/-- The restriction map of `modulePresheaf p ℱ` is the canonical semilinear
pullback-sections map. -/
theorem modulePresheaf_map
    (p : C ⥤ Over S) (ℱ : S.Modules) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (modulePresheaf p ℱ).map f = moduleMap p ℱ f := sorry

end ModulePresheaf

end AlgebraicGeometry.Scheme.Modules.PullbackSections
