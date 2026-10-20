/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Definition_60_11_1_ModuleProperties
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline

@[expose] public section

universe u

namespace CrystallineModuleSheaf

/-- Definition 60.11.1 (1): for either the big crystalline category `CRIS(X/S)`
or the small crystalline category `Cris(X/S)`, local quasi-coherence means that
the module assigned to every crystalline object is quasi-coherent. -/
@[stacks 07IS]
theorem isLocallyQuasiCoherent_iff
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀) :
    IsLocallyQuasiCoherent F ↔
      ∀ A : CRIS S I γ h_compatible X x₀, (F.obj A).IsQuasicoherent := sorry

/-- Definition 60.11.1 (2), `Cris(X/S)` specialization: the same
objectwise characterization for module-sheaf data on the small crystalline site. -/
@[stacks 07IS]
theorem isLocallyQuasiCoherent_iff_Cris
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    CrisModuleSheaf.IsLocallyQuasiCoherent F ↔
      ∀ A : smallCrystallineSite S I γ h_compatible X x₀,
        (F.obj A).IsQuasicoherent := sorry

/- Definition 60.11.1 (3): quasi-coherence in the sense of Modules on Sites,
as in Definition 18.23.1. -/
@[stacks 07IS] #check @SheafOfModules.IsQuasicoherent

/-- Definition 60.11.1 (4): for the big crystalline category, a module sheaf is
a crystal when every comparison morphism is an isomorphism. -/
@[stacks 07IS]
theorem isCrystal_iff
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀) :
    IsCrystal F ↔
      ∀ {A B : CRIS S I γ h_compatible X x₀}
        (f : CrystallineObject.Hom A B), IsIso (F.comparison f) := sorry

/-- Definition 60.11.1 (5), `Cris(X/S)` specialization: every comparison
morphism in the small crystalline category is an isomorphism. -/
@[stacks 07IS]
theorem isCrystal_iff_Cris
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    CrisModuleSheaf.IsCrystal F ↔
      ∀ {A B : smallCrystallineSite S I γ h_compatible X x₀}
        (f : A ⟶ B), IsIso (F.comparison f) := sorry

end CrystallineModuleSheaf

end
