module

public import stacks_project.Chap60.«60_10_0_2_ModuleSheaf»
public import stacks_project.Chap60.«60_9_1_1_Site»
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline

@[expose] public section

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

universe u v

/-- Construct module-sheaf data from its objectwise assignments and comparison maps. -/
def ModuleSheaf.of
    {C : Type v} [Category C]
    (thickening : C → Scheme.{u})
    (thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B))
    (obj : ∀ A : C, (thickening A).Modules)
    (comparison : ∀ {A B : C} (f : A ⟶ B),
      (Scheme.Modules.pullback (thickeningMap f)).obj (obj B) ⟶ obj A) :
    ModuleSheaf C thickening thickeningMap :=
  { obj, comparison }

/-- The objectwise field of `ModuleSheaf.of`. -/
theorem ModuleSheaf.of_obj
    {C : Type v} [Category C]
    (thickening : C → Scheme.{u})
    (thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B))
    (obj : ∀ A : C, (thickening A).Modules)
    (comparison : ∀ {A B : C} (f : A ⟶ B),
      (Scheme.Modules.pullback (thickeningMap f)).obj (obj B) ⟶ obj A) :
    ∀ A : C, (ModuleSheaf.of thickening thickeningMap obj comparison).obj A = obj A := sorry

/-- The comparison field of `ModuleSheaf.of`. -/
theorem ModuleSheaf.of_comparison
    {C : Type v} [Category C]
    (thickening : C → Scheme.{u})
    (thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B))
    (obj : ∀ A : C, (thickening A).Modules)
    (comparison : ∀ {A B : C} (f : A ⟶ B),
      (Scheme.Modules.pullback (thickeningMap f)).obj (obj B) ⟶ obj A)
    {A B : C} (f : A ⟶ B) :
    (ModuleSheaf.of thickening thickeningMap obj comparison).comparison f = comparison f := sorry

/-- Local quasi-coherence for module-sheaf data on the selected crystalline category. -/
class ModuleSheaf.IsLocallyQuasiCoherent
    {C : Type v} [Category C]
    {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    (F : ModuleSheaf C thickening thickeningMap) : Prop where
  /-- Every assigned module sheaf is quasi-coherent. -/
  objectwise : ∀ A : C, (F.obj A).IsQuasicoherent

/-- The objectwise quasi-coherence consequence of local quasi-coherence. -/
instance ModuleSheaf.IsLocallyQuasiCoherent.object_isQuasicoherent
    {C : Type v} [Category C]
    {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    {F : ModuleSheaf C thickening thickeningMap}
    [hF : F.IsLocallyQuasiCoherent] (A : C) : (F.obj A).IsQuasicoherent :=
  hF.objectwise A

/-- The defining objectwise characterization of local quasi-coherence. -/
theorem ModuleSheaf.isLocallyQuasiCoherent_iff
    {C : Type v} [Category C]
    {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    (F : ModuleSheaf C thickening thickeningMap) :
    F.IsLocallyQuasiCoherent ↔ ∀ A : C, (F.obj A).IsQuasicoherent := sorry

/-- The crystal property for module-sheaf data on the selected crystalline category. -/
class ModuleSheaf.IsCrystal
    {C : Type v} [Category C]
    {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    (F : ModuleSheaf C thickening thickeningMap) : Prop where
  /-- Every comparison morphism is an isomorphism. -/
  comparison_isIso : ∀ {A B : C} (f : A ⟶ B), IsIso (F.comparison f)

/-- The comparison-isomorphism consequence of the crystal property. -/
instance ModuleSheaf.IsCrystal.comparisonIsIso
    {C : Type v} [Category C]
    {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    {F : ModuleSheaf C thickening thickeningMap}
    [hF : F.IsCrystal] {A B : C} (f : A ⟶ B) : IsIso (F.comparison f) :=
  hF.comparison_isIso f

/-- The defining comparison-isomorphism characterization of crystals. -/
theorem ModuleSheaf.isCrystal_iff
    {C : Type v} [Category C]
    {thickening : C → Scheme.{u}}
    {thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B)}
    (F : ModuleSheaf C thickening thickeningMap) :
    F.IsCrystal ↔ ∀ {A B : C} (f : A ⟶ B), IsIso (F.comparison f) := sorry

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
    (F.toModuleSheaf.obj A) = F.obj A := sorry

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

/-- The objectwise quasi-coherence consequence for a big crystalline module sheaf. -/
instance IsLocallyQuasiCoherent.object_isQuasicoherent
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {F : CrystallineModuleSheaf S I γ h_compatible X x₀}
    [hF : IsLocallyQuasiCoherent F]
    (A : CRIS S I γ h_compatible X x₀) : (F.obj A).IsQuasicoherent :=
  ModuleSheaf.IsLocallyQuasiCoherent.object_isQuasicoherent
    (F := F.toModuleSheaf) A

/-- The comparison-isomorphism consequence for a big crystalline module sheaf. -/
instance IsCrystal.comparisonIsIso
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {F : CrystallineModuleSheaf S I γ h_compatible X x₀}
    [hF : IsCrystal F]
    {A B : CRIS S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B) : IsIso (F.comparison f) :=
  ModuleSheaf.IsCrystal.comparisonIsIso (F := F.toModuleSheaf) f

/-- The module-sheaf data for the small crystalline category `Cris(X/S)`. -/
abbrev CrisModuleSheaf
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :=
  ModuleSheaf (smallCrystallineSite S I γ h_compatible X x₀)
    (fun A ↦ A.obj.1.thickening)
    (fun {A B} (f : A ⟶ B) ↦ f.hom.thickening)

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
        (F.obj A).IsQuasicoherent := sorry

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
        (f : A ⟶ B), IsIso (F.comparison f) := sorry

end CrisModuleSheaf

end CrystallineModuleSheaf

end
