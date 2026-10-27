/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Module.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Crystal

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf SheafOfModules

@[expose] public section

universe u

/-- a sheaf of modules on `CRIS(X/S)` is quasi-coherent if and only if it is locally
quasi-coherent and a crystal in `𝒪_{X/S}`-modules. -/
theorem CrystallineModuleSheaf.isQuasiCoherent_iff_isLocallyQuasiCoherent_and_isCrystal
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    [h_sheafify :
      ∀ A : RelativeCRIS S I γ h_compatible X x₀,
        HasWeakSheafify
          ((crystallineZariskiTopology S I γ h_compatible X x₀).over A)
          AddCommGrpCat.{u}]
    [h_locally_bijective :
      ∀ A : RelativeCRIS S I γ h_compatible X x₀,
        ((crystallineZariskiTopology S I γ h_compatible X x₀).over A).WEqualsLocallyBijective
          AddCommGrpCat.{u}]
    (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))) :
    F.IsQuasicoherent ↔
      ModuleSheaf.IsLocallyQuasiCoherent (restrict F) ∧ ModuleSheaf.IsCrystal (restrict F) := sorry

/-- a sheaf of modules on `Cris(X/S)` is quasi-coherent if and only if it is locally
quasi-coherent and a crystal in `𝒪_{X/S}`-modules. -/
theorem CrystallineModuleSheaf.CrisModuleSheaf.isQuasiCoherent_iff_isLocallyQuasiCoherent_and_isCrystal
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    [h_sheafify :
      ∀ A : smallCrystallineSite S I γ h_compatible X x₀,
        HasWeakSheafify
          ((@smallCrystallineZariskiTopology S I γ h_compatible X x₀).over A)
          AddCommGrpCat.{u}]
    [h_locally_bijective :
      ∀ A : smallCrystallineSite S I γ h_compatible X x₀,
        ((@smallCrystallineZariskiTopology S I γ h_compatible X x₀).over A).WEqualsLocallyBijective
          AddCommGrpCat.{u}]
    (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))) :
    F.IsQuasicoherent ↔
      CrisModuleSheaf.IsLocallyQuasiCoherent (CrisModuleSheaf.restrict F) ∧
        CrisModuleSheaf.IsCrystal (CrisModuleSheaf.restrict F) := sorry

/-- a sheaf of modules on `CRIS(X/S)` is a crystal in
quasi-coherent modules if and only if it is quasi-coherent, equivalently locally
quasi-coherent and a crystal in `𝒪_{X/S}`-modules. -/
theorem CrystallineModuleSheaf.isCrystalInQuasiCoherentModules_iff
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    [h_sheafify :
      ∀ A : RelativeCRIS S I γ h_compatible X x₀,
        HasWeakSheafify
          ((crystallineZariskiTopology S I γ h_compatible X x₀).over A)
          AddCommGrpCat.{u}]
    [h_locally_bijective :
      ∀ A : RelativeCRIS S I γ h_compatible X x₀,
        ((crystallineZariskiTopology S I γ h_compatible X x₀).over A).WEqualsLocallyBijective
          AddCommGrpCat.{u}]
    (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))) :
    IsCrystalInQuasiCoherentModules F ↔
      F.IsQuasicoherent ∧
        ModuleSheaf.IsLocallyQuasiCoherent (restrict F) ∧ ModuleSheaf.IsCrystal (restrict F) := by
  rw [SheafOfModules.isCrystalInQuasiCoherentModules_iff F]
  exact ⟨fun h => ⟨h, (CrystallineModuleSheaf.isQuasiCoherent_iff_isLocallyQuasiCoherent_and_isCrystal F).mp h⟩, fun h => h.1⟩

/-- a sheaf of modules on `Cris(X/S)` is a crystal in
quasi-coherent modules if and only if it is quasi-coherent, equivalently locally
quasi-coherent and a crystal in `𝒪_{X/S}`-modules. -/
theorem CrystallineModuleSheaf.CrisModuleSheaf.isCrystalInQuasiCoherentModules_iff
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    [h_sheafify :
      ∀ A : smallCrystallineSite S I γ h_compatible X x₀,
        HasWeakSheafify
          ((@smallCrystallineZariskiTopology S I γ h_compatible X x₀).over A)
          AddCommGrpCat.{u}]
    [h_locally_bijective :
      ∀ A : smallCrystallineSite S I γ h_compatible X x₀,
        ((@smallCrystallineZariskiTopology S I γ h_compatible X x₀).over A).WEqualsLocallyBijective
          AddCommGrpCat.{u}]
    (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))) :
    IsCrystalInQuasiCoherentModules F ↔
      F.IsQuasicoherent ∧
        CrisModuleSheaf.IsLocallyQuasiCoherent (CrisModuleSheaf.restrict F) ∧
          CrisModuleSheaf.IsCrystal (CrisModuleSheaf.restrict F) := by
  rw [SheafOfModules.isCrystalInQuasiCoherentModules_iff F]
  exact ⟨fun h => ⟨h, (CrisModuleSheaf.isQuasiCoherent_iff_isLocallyQuasiCoherent_and_isCrystal F).mp h⟩, fun h => h.1⟩

end
