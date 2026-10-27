/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

private lemma sectionsMap_comp {X : Scheme.{u}} {F G H : X.Modules}
    (α : F ⟶ G) (β : G ⟶ H) :
    globalSectionsMap (α ≫ β) = globalSectionsMap α ≫ globalSectionsMap β := rfl

private lemma sectionsMap_eqToHom {X : Scheme.{u}} {F G : X.Modules} (e : F = G) :
    globalSectionsMap (eqToHom e) = eqToHom (congrArg globalSections e) := by
  subst G
  rfl

private lemma naturality {X Y : Scheme.{u}} (f : X ⟶ Y) {F G : Y.Modules} (α : F ⟶ G) :
    globalSectionsMap α ≫ globalSectionsPullback f G =
      globalSectionsPullback f F ≫ globalSectionsMap ((pullback f).map α) := by
  have h := (pullbackPushforwardAdjunction f).unit.naturality α
  have htop := congrArg (fun φ ↦ Hom.app φ ⊤) h
  exact htop

private lemma comp_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules) :
    globalSectionsPullback g F ≫ globalSectionsPullback f ((pullback g).obj F) =
      globalSectionsPullback (f ≫ g) F ≫ globalSectionsMap ((pullbackComp f g).inv.app F) := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv F
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have htop := congrArg (fun φ ↦ Hom.app φ ⊤) h
  exact htop

set_option backward.isDefEq.respectTransparency false in
private lemma comp_coherence {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Z.Modules) :
    (pullbackComp f g).inv.app ((pullback h).obj F) ≫
      (pullback f).map ((pullbackComp g h).hom.app F) ≫
      (pullbackComp f (g ≫ h)).hom.app F ≫
      eqToHom (congrArg (fun k ↦ (pullback k).obj F) (Category.assoc f g h).symm) =
      (pullbackComp (f ≫ g) h).hom.app F := by
  have hc := congrArg (fun α ↦ α.app F) (pseudofunctor_associativity f g h)
  change (pullbackComp f (g ≫ h)).inv.app F ≫
    (pullback f).map ((pullbackComp g h).inv.app F) ≫ 𝟙 _ ≫
    (pullbackComp f g).hom.app ((pullback h).obj F) ≫
    (pullbackComp (f ≫ g) h).hom.app F =
    eqToHom (congrArg (fun k ↦ (pullback k).obj F) (Category.assoc f g h).symm) at hc
  simp only [Category.id_comp] at hc
  have hc' := congrArg (fun k ↦
    (pullbackComp f g).inv.app ((pullback h).obj F) ≫
      (pullback f).map ((pullbackComp g h).hom.app F) ≫
      (pullbackComp f (g ≫ h)).hom.app F ≫ k) hc
  have hcancel {Q : W.Modules}
      (k : (pullback f).obj ((pullback g).obj ((pullback h).obj F)) ⟶ Q) :
      (pullback f).map ((pullbackComp g h).hom.app F) ≫
        (pullback f).map ((pullbackComp g h).inv.app F) ≫ k = k := by
    rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    change (pullback f).map (𝟙 ((pullback g).obj ((pullback h).obj F))) ≫ k = k
    rw [(pullback f).map_id, Category.id_comp]
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    hcancel, eqToHom_app] using hc'.symm

set_option backward.isDefEq.respectTransparency false in
private lemma comp_sections {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Z.Modules) :
    globalSectionsPullbackComp g h F ≫ globalSectionsPullbackComp f (g ≫ h) F ≫
      eqToHom (congrArg (fun k ↦ globalSections ((pullback k).obj F))
        (Category.assoc f g h).symm) =
      globalSectionsPullbackComp (f ≫ g) h F := by
  let e := eqToHom (congrArg (fun k ↦ globalSections ((pullback k).obj F))
    (Category.assoc f g h).symm)
  have hc : globalSectionsMap ((pullbackComp f g).inv.app ((pullback h).obj F)) ≫
      globalSectionsMap ((pullback f).map ((pullbackComp g h).hom.app F)) ≫
      globalSectionsMap ((pullbackComp f (g ≫ h)).hom.app F) ≫
      eqToHom (congrArg (fun k ↦ globalSections ((pullback k).obj F))
        (Category.assoc f g h).symm) =
      globalSectionsMap ((pullbackComp (f ≫ g) h).hom.app F) := by
    simpa only [sectionsMap_comp, sectionsMap_eqToHom] using
      congrArg (fun φ ↦ globalSectionsMap φ) (comp_coherence f g h F)
  dsimp only [globalSectionsPullbackComp]
  calc
    _ = globalSectionsPullback g ((pullback h).obj F) ≫
        (globalSectionsPullback f ((pullback g).obj ((pullback h).obj F)) ≫
          globalSectionsMap ((pullback f).map ((pullbackComp g h).hom.app F))) ≫
        globalSectionsMap ((pullbackComp f (g ≫ h)).hom.app F) ≫ e := by
      rw [← naturality]
      simp only [Category.assoc, e]
    _ = (globalSectionsPullback g ((pullback h).obj F) ≫
          globalSectionsPullback f ((pullback g).obj ((pullback h).obj F))) ≫
        globalSectionsMap ((pullback f).map ((pullbackComp g h).hom.app F)) ≫
        globalSectionsMap ((pullbackComp f (g ≫ h)).hom.app F) ≫ e := by
      simp only [Category.assoc]
    _ = (globalSectionsPullback (f ≫ g) ((pullback h).obj F) ≫
          globalSectionsMap ((pullbackComp f g).inv.app ((pullback h).obj F))) ≫
        globalSectionsMap ((pullback f).map ((pullbackComp g h).hom.app F)) ≫
        globalSectionsMap ((pullbackComp f (g ≫ h)).hom.app F) ≫ e := by
      rw [comp_unit]
    _ = globalSectionsPullback (f ≫ g) ((pullback h).obj F) ≫
        globalSectionsMap ((pullbackComp (f ≫ g) h).hom.app F) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ globalSectionsPullback (f ≫ g) ((pullback h).obj F) ≫ k) hc

set_option backward.isDefEq.respectTransparency false in
/-- The restriction map on pullback-module global sections is the identity on an identity
morphism over `S`. -/
theorem map_id (ℱ : S.Modules) (A : Over S) : map ℱ (𝟙 A) = 𝟙 _ := by
  have hcomp : (pullbackComp (𝟙 A.left) A.hom).hom.app ℱ ≫
      eqToHom (congrArg (fun f ↦ (pullback f).obj ℱ) (Category.id_comp A.hom)) =
      (pullbackId A.left).hom.app ((pullback A.hom).obj ℱ) := by
    apply (cancel_epi ((pullbackComp (𝟙 A.left) A.hom).inv.app ℱ)).mp
    have h := congrArg (fun α ↦ α.app ℱ) (pseudofunctor_right_unitality A.hom)
    change (pullbackComp (𝟙 A.left) A.hom).inv.app ℱ ≫
      (pullbackId A.left).hom.app ((pullback A.hom).obj ℱ) ≫ 𝟙 _ =
      eqToHom (congrArg (fun k ↦ (pullback k).obj ℱ) (Category.id_comp A.hom)) at h
    simpa only [Category.comp_id, Iso.inv_hom_id_app_assoc] using h.symm
  have hcompG : globalSectionsMap ((pullbackComp (𝟙 A.left) A.hom).hom.app ℱ) ≫
      eqToHom (congrArg
        (fun f ↦ globalSections ((pullback f).obj ℱ)) (Category.id_comp A.hom)) =
      globalSectionsMap ((pullbackId A.left).hom.app ((pullback A.hom).obj ℱ)) := by
    simpa only [sectionsMap_comp, sectionsMap_eqToHom] using
      congrArg (fun φ ↦ globalSectionsMap φ) hcomp
  have h := unit_conjugateEquiv Adjunction.id (pullbackPushforwardAdjunction (𝟙 A.left))
    (pullbackId A.left).hom ((pullback A.hom).obj ℱ)
  rw [conjugateEquiv_pullbackId_hom] at h
  have htop := congrArg (fun φ ↦ Hom.app φ ⊤) h
  change (𝟙 (globalSections ((pullback A.hom).obj ℱ))) =
    globalSectionsPullback (𝟙 A.left) ((pullback A.hom).obj ℱ) ≫
      globalSectionsMap ((pullbackId A.left).hom.app ((pullback A.hom).obj ℱ)) at htop
  unfold map globalSectionsPullbackComp
  simp only [Over.id_left]
  rw [Category.assoc, hcompG]
  exact htop.symm

/-- Restriction maps on pullback-module global sections respect composition over `S`. -/
theorem map_comp (ℱ : S.Modules) {A B C : Over S} (φ : A ⟶ B) (ψ : B ⟶ C) :
    map ℱ (φ ≫ ψ) = map ℱ ψ ≫ map ℱ φ := by
  dsimp only [map]
  simp only [Category.assoc]
  rw [← eqToHom_naturality_assoc (fun k ↦ globalSectionsPullbackComp φ.left k ℱ) (Over.w ψ)]
  have hs := congrArg
    (fun k ↦ k ≫ eqToHom (congrArg
      (fun k ↦ globalSections ((pullback k).obj ℱ)) (Over.w (φ ≫ ψ))))
    (comp_sections φ.left ψ.left C.hom ℱ)
  simpa only [Category.assoc, eqToHom_trans, Over.comp_left] using hs.symm

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
      Scheme.Modules.globalSections ((Scheme.Modules.pullback A.hom).obj ℱ) := rfl

/-- The action of `over S ℱ` on a morphism over `S` is the corresponding restriction map. -/
theorem over_map (S : Scheme.{u}) (ℱ : S.Modules) {A B : Over S} (φ : A ⟶ B) :
    (over S ℱ).map φ.op = map ℱ φ := rfl

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
        ((map ℱ (p.map f.unop)).hom s) := by
  let φ := p.map f.unop
  have h (a : (p.obj V.unop).left ⟶ S)
      (ha : φ.left ≫ (p.obj U.unop).hom = a) :
      (Scheme.Modules.globalSectionsPullbackComp φ.left (p.obj U.unop).hom ℱ ≫
        eqToHom (congrArg
          (fun k ↦ Scheme.Modules.globalSections ((Scheme.Modules.pullback k).obj ℱ)) ha)).hom
            (r • s) =
      φ.left.appTop.hom r •
        (Scheme.Modules.globalSectionsPullbackComp φ.left (p.obj U.unop).hom ℱ ≫
          eqToHom (congrArg
            (fun k ↦ Scheme.Modules.globalSections ((Scheme.Modules.pullback k).obj ℱ)) ha)).hom
              s := by
    subst a
    change (Scheme.Modules.globalSectionsMap
      ((Scheme.Modules.pullbackComp φ.left (p.obj U.unop).hom).hom.app ℱ)).hom
        ((Scheme.Modules.globalSectionsPullback φ.left
          ((Scheme.Modules.pullback (p.obj U.unop).hom).obj ℱ)).hom (r • s)) = _
    have hunit :
        (Scheme.Modules.globalSectionsPullback φ.left
          ((Scheme.Modules.pullback (p.obj U.unop).hom).obj ℱ)).hom (r • s) =
        φ.left.appTop.hom r •
          (Scheme.Modules.globalSectionsPullback φ.left
            ((Scheme.Modules.pullback (p.obj U.unop).hom).obj ℱ)).hom s :=
      (((Scheme.Modules.pullbackPushforwardAdjunction φ.left).unit.app
        ((Scheme.Modules.pullback (p.obj U.unop).hom).obj ℱ)).val.app (op ⊤)).hom.map_smul r s
    rw [hunit]
    exact ((((Scheme.Modules.pullbackComp φ.left (p.obj U.unop).hom).hom.app ℱ).val.app
      (op ⊤)).hom.map_smul _ _)
  exact h _ (Over.w φ)

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
          ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map_id U))).inv.app _ := by
  ext s
  change (map ℱ (p.map (𝟙 U.unop))).hom s = s
  rw [p.map_id, map_id]
  rfl

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
            ((Scheme.Site.structurePresheaf (p ⋙ Over.forget S)).map_comp f g))).inv.app _ := by
  ext s
  change (map ℱ (p.map (g.unop ≫ f.unop))).hom s =
    (map ℱ (p.map g.unop)).hom ((map ℱ (p.map f.unop)).hom s)
  rw [p.map_comp, map_comp]
  rfl

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
    (modulePresheaf p ℱ).obj U = moduleObj p ℱ U := rfl

/-- The restriction map of `modulePresheaf p ℱ` is the canonical semilinear
pullback-sections map. -/
theorem modulePresheaf_map
    (p : C ⥤ Over S) (ℱ : S.Modules) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (modulePresheaf p ℱ).map f = moduleMap p ℱ f := rfl

end ModulePresheaf

end AlgebraicGeometry.Scheme.Modules.PullbackSections
