/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Quasicoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf
open scoped AlgebraicGeometry

universe u v w

/- Lemma 60.11.2 (1) -/
@[stacks 07IT]
#check (CrystallineModuleSheaf.isQuasiCoherent_iff_isLocallyQuasiCoherent_and_isCrystal : ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
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
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))),
    F.IsQuasicoherent ↔
      ModuleSheaf.IsLocallyQuasiCoherent (restrict F) ∧ ModuleSheaf.IsCrystal (restrict F))

/- Lemma 60.11.2 (2) -/
@[stacks 07IT]
#check (CrystallineModuleSheaf.CrisModuleSheaf.isQuasiCoherent_iff_isLocallyQuasiCoherent_and_isCrystal : ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
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
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))),
    F.IsQuasicoherent ↔
      CrisModuleSheaf.IsLocallyQuasiCoherent (CrisModuleSheaf.restrict F) ∧
        CrisModuleSheaf.IsCrystal (CrisModuleSheaf.restrict F))

