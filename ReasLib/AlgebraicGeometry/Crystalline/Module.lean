/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Site
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline

/-- A crystalline module sheaf assigns a module sheaf to each crystalline thickening and a
comparison morphism to every morphism of crystalline-site objects. -/
structure CrystallineModuleSheaf.{u}
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) where
  /-- The module sheaf on the thickening of a crystalline-site object. -/
  obj : ∀ A : CRIS S I γ h_compatible X x₀, A.thickening.Modules
  /-- The comparison morphism induced by a morphism of crystalline-site objects. -/
  comparison : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (f : CrystallineObject.Hom A B),
    (Scheme.Modules.pullback f.thickening).obj (obj B) ⟶ obj A


  /-- The identity comparison is the canonical pullback identification. -/
  comparison_id : ∀ A : CRIS S I γ h_compatible X x₀,
    comparison (CrystallineObject.Hom.id A) =
      (Scheme.Modules.pullbackId A.thickening).hom.app (obj A)
  /-- The composition comparison is obtained by composing the two comparisons. -/
  comparison_comp : ∀ {A B C : CRIS S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B) (g : CrystallineObject.Hom B C),
    comparison (CrystallineObject.Hom.comp f g) =
      (Scheme.Modules.pullbackComp f.thickening g.thickening).inv.app (obj C) ≫
        (Scheme.Modules.pullback f.thickening).map (comparison g) ≫ comparison f

/-- Construct a crystalline module sheaf from its objectwise module sheaves and comparison family. -/
def CrystallineModuleSheaf.of
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (obj : ∀ A : CRIS S I γ h_compatible X x₀, A.thickening.Modules)
    (comparison : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (f : CrystallineObject.Hom A B),
      (Scheme.Modules.pullback f.thickening).obj (obj B) ⟶ obj A)
    (comparison_id : ∀ A : CRIS S I γ h_compatible X x₀,
    comparison (CrystallineObject.Hom.id A) =
      (Scheme.Modules.pullbackId A.thickening).hom.app (obj A))
    (comparison_comp : ∀ {A B C : CRIS S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B) (g : CrystallineObject.Hom B C),
    comparison (CrystallineObject.Hom.comp f g) =
      (Scheme.Modules.pullbackComp f.thickening g.thickening).inv.app (obj C) ≫
        (Scheme.Modules.pullback f.thickening).map (comparison g) ≫ comparison f) :
    CrystallineModuleSheaf S I γ h_compatible X x₀ :=
  { obj, comparison, comparison_id, comparison_comp }

/-- Crystalline comparison morphisms preserve identities and composition. -/
theorem CrystallineModuleSheaf.spec
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀) :
    (∀ A : CRIS S I γ h_compatible X x₀,
      F.comparison (CrystallineObject.Hom.id A) =
        (Scheme.Modules.pullbackId A.thickening).hom.app (F.obj A)) ∧
    (∀ {A B C : CRIS S I γ h_compatible X x₀}
      (f : CrystallineObject.Hom A B) (g : CrystallineObject.Hom B C),
      F.comparison (CrystallineObject.Hom.comp f g) =
        (Scheme.Modules.pullbackComp f.thickening g.thickening).inv.app (F.obj C) ≫
          (Scheme.Modules.pullback f.thickening).map (F.comparison g) ≫ F.comparison f) :=
  ⟨F.comparison_id, F.comparison_comp⟩

namespace CrystallineModuleSheaf

/-- A module-sheaf assignment on a chosen crystalline category, including the
comparison maps induced by its thickening morphisms. -/
structure ModuleSheaf.{u, v} (C : Type v) [Category C]
    (thickening : C → Scheme.{u})
    (thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)) where
  /-- The module sheaf assigned to each object. -/
  obj : ∀ A : C, (thickening A).Modules
  /-- The comparison morphism assigned to each category morphism. -/
  comparison : ∀ {A B : C} (f : A ⟶ B),
    (Scheme.Modules.pullback (thickeningMap f)).obj (obj B) ⟶ obj A

  /-- The thickening map preserves identity morphisms. -/
  map_id : ∀ A : C, thickeningMap (𝟙 A) = 𝟙 (thickening A)
  /-- The thickening map preserves composition. -/
  map_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
    thickeningMap (f ≫ g) = thickeningMap f ≫ thickeningMap g
  /-- Identity comparisons agree with canonical pullback along the identity. -/
  comparison_id : ∀ A : C,
    comparison (𝟙 A) =
      (Scheme.Modules.pullbackCongr (map_id A)).hom.app (obj A) ≫
        (Scheme.Modules.pullbackId (thickening A)).hom.app (obj A)
  /-- Comparison maps respect composition and the canonical pullback compositor. -/
  comparison_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
    comparison (f ≫ g) =
      (Scheme.Modules.pullbackCongr (map_comp f g)).hom.app (obj D) ≫
        (Scheme.Modules.pullbackComp (thickeningMap f) (thickeningMap g)).inv.app (obj D) ≫
        (Scheme.Modules.pullback (thickeningMap f)).map (comparison g) ≫ comparison f

universe u v

/-- Construct module-sheaf data from its objectwise assignments and comparison maps. -/
def ModuleSheaf.of
    {C : Type v} [Category C]
    (thickening : C → Scheme.{u})
    (thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B))
    (obj : ∀ A : C, (thickening A).Modules)
    (comparison : ∀ {A B : C} (f : A ⟶ B),
      (Scheme.Modules.pullback (thickeningMap f)).obj (obj B) ⟶ obj A)
    (map_id : ∀ A : C, thickeningMap (𝟙 A) = 𝟙 (thickening A))
    (map_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
      thickeningMap (f ≫ g) = thickeningMap f ≫ thickeningMap g)
    (comparison_id : ∀ A : C, comparison (𝟙 A) =
      (Scheme.Modules.pullbackCongr (map_id A)).hom.app (obj A) ≫
        (Scheme.Modules.pullbackId (thickening A)).hom.app (obj A))
    (comparison_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
      comparison (f ≫ g) =
        (Scheme.Modules.pullbackCongr (map_comp f g)).hom.app (obj D) ≫
          (Scheme.Modules.pullbackComp (thickeningMap f) (thickeningMap g)).inv.app (obj D) ≫
          (Scheme.Modules.pullback (thickeningMap f)).map (comparison g) ≫ comparison f)
 :
    ModuleSheaf C thickening thickeningMap :=
  { obj, comparison, map_id, map_comp, comparison_id, comparison_comp }

/-- The objectwise field of `ModuleSheaf.of`. -/
theorem ModuleSheaf.of_obj
    {C : Type v} [Category C]
    (thickening : C → Scheme.{u})
    (thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B))
    (obj : ∀ A : C, (thickening A).Modules)
    (comparison : ∀ {A B : C} (f : A ⟶ B),
      (Scheme.Modules.pullback (thickeningMap f)).obj (obj B) ⟶ obj A)
    (map_id : ∀ A : C, thickeningMap (𝟙 A) = 𝟙 (thickening A))
    (map_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
      thickeningMap (f ≫ g) = thickeningMap f ≫ thickeningMap g)
    (comparison_id : ∀ A : C, comparison (𝟙 A) =
      (Scheme.Modules.pullbackCongr (map_id A)).hom.app (obj A) ≫
        (Scheme.Modules.pullbackId (thickening A)).hom.app (obj A))
    (comparison_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
      comparison (f ≫ g) =
        (Scheme.Modules.pullbackCongr (map_comp f g)).hom.app (obj D) ≫
          (Scheme.Modules.pullbackComp (thickeningMap f) (thickeningMap g)).inv.app (obj D) ≫
          (Scheme.Modules.pullback (thickeningMap f)).map (comparison g) ≫ comparison f)
 :
    ∀ A : C, (ModuleSheaf.of thickening thickeningMap obj comparison map_id map_comp comparison_id comparison_comp).obj A = obj A := fun _ => rfl

/-- The comparison field of `ModuleSheaf.of`. -/
theorem ModuleSheaf.of_comparison
    {C : Type v} [Category C]
    (thickening : C → Scheme.{u})
    (thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B))
    (obj : ∀ A : C, (thickening A).Modules)
    (comparison : ∀ {A B : C} (f : A ⟶ B),
      (Scheme.Modules.pullback (thickeningMap f)).obj (obj B) ⟶ obj A)
    (map_id : ∀ A : C, thickeningMap (𝟙 A) = 𝟙 (thickening A))
    (map_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
      thickeningMap (f ≫ g) = thickeningMap f ≫ thickeningMap g)
    (comparison_id : ∀ A : C, comparison (𝟙 A) =
      (Scheme.Modules.pullbackCongr (map_id A)).hom.app (obj A) ≫
        (Scheme.Modules.pullbackId (thickening A)).hom.app (obj A))
    (comparison_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
      comparison (f ≫ g) =
        (Scheme.Modules.pullbackCongr (map_comp f g)).hom.app (obj D) ≫
          (Scheme.Modules.pullbackComp (thickeningMap f) (thickeningMap g)).inv.app (obj D) ≫
          (Scheme.Modules.pullback (thickeningMap f)).map (comparison g) ≫ comparison f)

    {A B : C} (f : A ⟶ B) :
    (ModuleSheaf.of thickening thickeningMap obj comparison map_id map_comp comparison_id comparison_comp).comparison f = comparison f := rfl

/-- The thickening maps and coefficient comparisons preserve identities and composition. -/
theorem ModuleSheaf.spec
    {C : Type v} [Category C]
    {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    (F : ModuleSheaf C thickening thickeningMap) :
    (∀ A : C, thickeningMap (𝟙 A) = 𝟙 (thickening A)) ∧
    (∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
      thickeningMap (f ≫ g) = thickeningMap f ≫ thickeningMap g) ∧
    (∀ A : C, F.comparison (𝟙 A) =
      (Scheme.Modules.pullbackCongr (F.map_id A)).hom.app (F.obj A) ≫
        (Scheme.Modules.pullbackId (thickening A)).hom.app (F.obj A)) ∧
    (∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D), F.comparison (f ≫ g) =
      (Scheme.Modules.pullbackCongr (F.map_comp f g)).hom.app (F.obj D) ≫
        (Scheme.Modules.pullbackComp (thickeningMap f) (thickeningMap g)).inv.app (F.obj D) ≫
        (Scheme.Modules.pullback (thickeningMap f)).map (F.comparison g) ≫ F.comparison f) :=
  ⟨F.map_id, F.map_comp, F.comparison_id, F.comparison_comp⟩

/-- A coefficient family is locally quasi-coherent when every assigned module is quasi-coherent. -/
abbrev ModuleSheaf.IsLocallyQuasiCoherent
    {C : Type v} [Category C] {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    (F : ModuleSheaf C thickening thickeningMap) : Prop :=
  ∀ A : C, (F.obj A).IsQuasicoherent

/-- Local quasi-coherence is equivalent to objectwise quasi-coherence. -/
theorem ModuleSheaf.isLocallyQuasiCoherent_iff
    {C : Type v} [Category C] {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    (F : ModuleSheaf C thickening thickeningMap) :
    F.IsLocallyQuasiCoherent ↔ ∀ A : C, (F.obj A).IsQuasicoherent := Iff.rfl

/-- A coefficient family is a crystal when all of its comparison morphisms are invertible. -/
abbrev ModuleSheaf.IsCrystal
    {C : Type v} [Category C] {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    (F : ModuleSheaf C thickening thickeningMap) : Prop :=
  ∀ {A B : C} (f : A ⟶ B), IsIso (F.comparison f)

/-- Every comparison morphism of a crystal is invertible. -/
theorem ModuleSheaf.IsCrystal.comparison_isIso
    {C : Type v} [Category C] {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    {F : ModuleSheaf C thickening thickeningMap} [hF : ModuleSheaf.IsCrystal F]
    {A B : C} (f : A ⟶ B) : IsIso (F.comparison f) :=
  hF f

/-- The crystal condition is equivalent to invertibility of each comparison. -/
theorem ModuleSheaf.isCrystal_iff
    {C : Type v} [Category C] {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    (F : ModuleSheaf C thickening thickeningMap) :
    F.IsCrystal ↔ ∀ {A B : C} (f : A ⟶ B), IsIso (F.comparison f) := Iff.rfl

/-- The module-sheaf data underlying an existing big crystalline module sheaf. -/
def toModuleSheaf
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀) :
    ModuleSheaf (CRIS S I γ h_compatible X x₀)
      (fun A ↦ A.thickening)
      (fun {A B} (f : CrystallineObject.Hom A B) ↦ f.thickening) where
  obj := F.obj
  comparison := F.comparison
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl
  comparison_id := fun A => (F.comparison_id A).trans (Category.id_comp _).symm
  comparison_comp := fun f g => (F.comparison_comp f g).trans (Category.id_comp _).symm


/-- The objectwise module assignment of `CrystallineModuleSheaf.toModuleSheaf`. -/
theorem toModuleSheaf_obj
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
    (A : CRIS S I γ h_compatible X x₀) :
    (F.toModuleSheaf.obj A) = F.obj A := rfl

/-- Local quasi-coherence for a big crystalline module sheaf. -/
abbrev IsLocallyQuasiCoherent
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀) : Prop :=
  ModuleSheaf.IsLocallyQuasiCoherent F.toModuleSheaf

/-- The crystal property for a big crystalline module sheaf. -/
abbrev IsCrystal
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀) : Prop :=
  ModuleSheaf.IsCrystal F.toModuleSheaf

end CrystallineModuleSheaf

open CrystallineModuleSheaf

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- A morphism of module sheaves on `Cris(X / S)`. -/
structure CrisModuleSheafHom
    (F G : (CrystallineModuleSheaf.ModuleSheaf (smallCrystallineSite S I γ h_compatible X x₀)
      (fun A ↦ A.obj.1.thickening) (fun {A B} (f : A ⟶ B) ↦ f.hom.thickening))) where
  /-- The component on each small crystalline object. -/
  app : ∀ T : smallCrystallineSite S I γ h_compatible X x₀, F.obj T ⟶ G.obj T
  /-- Naturality with respect to morphisms of small crystalline objects. -/
  natural : ∀ {A B : smallCrystallineSite S I γ h_compatible X x₀}
      (f : A ⟶ B),
      (Scheme.Modules.pullback f.hom.thickening).map (app B) ≫ G.comparison f =
        F.comparison f ≫ app A

/-- Construct a morphism of `Cris(X / S)`-module sheaves from components. -/
def CrisModuleSheafHom.of
    {F G : (CrystallineModuleSheaf.ModuleSheaf (smallCrystallineSite S I γ h_compatible X x₀)
      (fun A ↦ A.obj.1.thickening) (fun {A B} (f : A ⟶ B) ↦ f.hom.thickening))}
    (app : ∀ T : smallCrystallineSite S I γ h_compatible X x₀, F.obj T ⟶ G.obj T)
    (natural : ∀ {A B : smallCrystallineSite S I γ h_compatible X x₀}
      (f : A ⟶ B),
      (Scheme.Modules.pullback f.hom.thickening).map (app B) ≫ G.comparison f =
        F.comparison f ≫ app A) :
    CrisModuleSheafHom F G :=
  { app, natural }

/-- The identity morphism of a `Cris(X / S)`-module sheaf. -/
def CrisModuleSheafHom.id (F : (CrystallineModuleSheaf.ModuleSheaf (smallCrystallineSite S I γ h_compatible X x₀)
      (fun A ↦ A.obj.1.thickening) (fun {A B} (f : A ⟶ B) ↦ f.hom.thickening))) :
    CrisModuleSheafHom F F :=
  CrisModuleSheafHom.of (fun T ↦ 𝟙 (F.obj T)) sorry

/-- Composition of morphisms of `Cris(X / S)`-module sheaves. -/
def CrisModuleSheafHom.comp
    {F G H : (CrystallineModuleSheaf.ModuleSheaf (smallCrystallineSite S I γ h_compatible X x₀)
      (fun A ↦ A.obj.1.thickening) (fun {A B} (f : A ⟶ B) ↦ f.hom.thickening))}
    (f : CrisModuleSheafHom F G) (g : CrisModuleSheafHom G H) :
    CrisModuleSheafHom F H :=
  CrisModuleSheafHom.of (fun T ↦ f.app T ≫ g.app T) sorry

/-- Composing a crystalline module-sheaf morphism after the identity leaves it unchanged. -/
theorem CrisModuleSheafHom.id_comp
    {F G : CrystallineModuleSheaf.ModuleSheaf (smallCrystallineSite S I γ h_compatible X x₀)
      (fun A ↦ A.obj.1.thickening) (fun {A B} (f : A ⟶ B) ↦ f.hom.thickening)}
    (f : CrisModuleSheafHom F G) :
    CrisModuleSheafHom.comp (CrisModuleSheafHom.id F) f = f := sorry

/-- Composing a crystalline module-sheaf morphism with the identity leaves it unchanged. -/
theorem CrisModuleSheafHom.comp_id
    {F G : CrystallineModuleSheaf.ModuleSheaf (smallCrystallineSite S I γ h_compatible X x₀)
      (fun A ↦ A.obj.1.thickening) (fun {A B} (f : A ⟶ B) ↦ f.hom.thickening)}
    (f : CrisModuleSheafHom F G) :
    CrisModuleSheafHom.comp f (CrisModuleSheafHom.id G) = f := sorry

/-- Composition of crystalline module-sheaf morphisms is associative. -/
theorem CrisModuleSheafHom.assoc
    {F G H K : CrystallineModuleSheaf.ModuleSheaf (smallCrystallineSite S I γ h_compatible X x₀)
      (fun A ↦ A.obj.1.thickening) (fun {A B} (f : A ⟶ B) ↦ f.hom.thickening)}
    (f : CrisModuleSheafHom F G) (g : CrisModuleSheafHom G H)
    (h : CrisModuleSheafHom H K) :
    CrisModuleSheafHom.comp (CrisModuleSheafHom.comp f g) h =
      CrisModuleSheafHom.comp f (CrisModuleSheafHom.comp g h) := sorry


namespace CrystallineModuleSheaf

/-- The category of coherent module coefficients on the small crystalline site. -/
def CrisModuleSheaf (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) : Cat.{u + 1, u + 1} :=
  @Cat.of.{u + 1, u + 1} ((CrystallineModuleSheaf.ModuleSheaf (smallCrystallineSite S I γ h_compatible X x₀)
      (fun A ↦ A.obj.1.thickening) (fun {A B} (f : A ⟶ B) ↦ f.hom.thickening)))
    { Hom := CrisModuleSheafHom
      id := CrisModuleSheafHom.id
      comp := fun {A B C} f g => CrisModuleSheafHom.comp (F := A) (G := B) (H := C) f g
      id_comp := CrisModuleSheafHom.id_comp
      comp_id := CrisModuleSheafHom.comp_id
      assoc := CrisModuleSheafHom.assoc }

namespace CrisModuleSheaf

/-- Local quasi-coherence for module-sheaf data on `Cris(X/S)`. -/
abbrev IsLocallyQuasiCoherent
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrisModuleSheaf S I γ h_compatible X x₀) : Prop :=
  ModuleSheaf.IsLocallyQuasiCoherent F

/-- The crystal property for module-sheaf data on `Cris(X/S)`. -/
abbrev IsCrystal
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrisModuleSheaf S I γ h_compatible X x₀) : Prop :=
  ModuleSheaf.IsCrystal F

/-- The objectwise characterization of local quasi-coherence on `Cris(X/S)`. -/
theorem isLocallyQuasiCoherent_iff
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    IsLocallyQuasiCoherent F ↔
      ∀ A : smallCrystallineSite S I γ h_compatible X x₀,
        (F.obj A).IsQuasicoherent := Iff.rfl

/-- The comparison-isomorphism characterization of crystals on `Cris(X/S)`. -/
theorem isCrystal_iff
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    IsCrystal F ↔
      ∀ {A B : smallCrystallineSite S I γ h_compatible X x₀}
        (f : A ⟶ B), IsIso (F.comparison f) := Iff.rfl

end CrisModuleSheaf

/-- Restriction of a big crystalline module assignment to the small crystalline site. -/
def restrictCrystallineModule (F : CrystallineModuleSheaf S I γ h_compatible X x₀) :
    CrisModuleSheaf S I γ h_compatible X x₀ where
  obj T := F.obj T.obj.1
  comparison f := F.comparison f.hom
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl
  comparison_id := fun T => (F.comparison_id T.obj.1).trans (Category.id_comp _).symm
  comparison_comp := fun f g => (F.comparison_comp f.hom g.hom).trans (Category.id_comp _).symm

/-- Restriction retains the module sheaf on each thickening. -/
theorem restrictCrystallineModule_obj
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (restrictCrystallineModule F).obj T = F.obj T.obj.1 := rfl


end CrystallineModuleSheaf

/-- Evaluation of a small crystalline module sheaf at an object of `Cris(X / S)`. -/
def crystallineEval
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (T.obj.1.thickening).Modules :=
  F.obj T

/-- Evaluation at `T` recovers the objectwise module sheaf. -/
theorem crystallineEval_eq
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    crystallineEval F T = F.obj T := rfl

/-- Evaluation at a fixed object `T` of `Cris(X / S)`, as a functor. -/
def crystallineEvalFunctor
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrisModuleSheaf S I γ h_compatible X x₀ ⥤ (T.obj.1.thickening).Modules where
  obj F := crystallineEval F T
  map f := CrisModuleSheafHom.app f T

/-- A morphism of crystalline module sheaves, with its comparison naturality. -/
structure CrystallineModuleMap.{u_1}
    (S : Scheme.{u_1}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u_1}) (x₀ : X ⟶ I.subscheme)
    (F G : CrystallineModuleSheaf S I γ h_compatible X x₀) where
  /-- The module morphism on each crystalline object. -/
  component : ∀ T : CRIS S I γ h_compatible X x₀, F.obj T ⟶ G.obj T
  /-- The components commute with the comparison maps of the crystalline site. -/
  natural : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (f : CrystallineObject.Hom A B),
      (Scheme.Modules.pullback f.thickening).map (component B) ≫ G.comparison f =
        F.comparison f ≫ component A

/-- Construct a natural morphism of crystalline module sheaves. -/
def CrystallineModuleMap.of
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (F G : CrystallineModuleSheaf S I γ h_compatible X x₀)
    (component : ∀ T : CRIS S I γ h_compatible X x₀, F.obj T ⟶ G.obj T)
    (natural : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (f : CrystallineObject.Hom A B),
      (Scheme.Modules.pullback f.thickening).map (component B) ≫ G.comparison f =
        F.comparison f ≫ component A) :
    CrystallineModuleMap S I γ h_compatible X x₀ F G :=
  { component, natural }


end
