/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Quasicoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf
open scoped AlgebraicGeometry

universe u v w

/- Definition 60.11.3 (1) -/
@[stacks 07IU]
#check (CrystallineModuleSheaf.isCrystalInQuasiCoherentModules_iff : ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
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
    IsCrystalInQuasiCoherentModules F ↔
      F.IsQuasicoherent ∧
        ModuleSheaf.IsLocallyQuasiCoherent (restrict F) ∧ ModuleSheaf.IsCrystal (restrict F))

/- Definition 60.11.3 (2) -/
@[stacks 07IU]
#check (CrystallineModuleSheaf.CrisModuleSheaf.isCrystalInQuasiCoherentModules_iff : ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
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
    IsCrystalInQuasiCoherentModules F ↔
      F.IsQuasicoherent ∧
        CrisModuleSheaf.IsLocallyQuasiCoherent (CrisModuleSheaf.restrict F) ∧
          CrisModuleSheaf.IsCrystal (CrisModuleSheaf.restrict F))

section

variable {S : Scheme.{u}} {I : S.IdealSheafData}
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
variable (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))

/- Definition 60.11.3 (3) -/
@[stacks 07IU]
#check (SheafOfModules.isCrystalInFiniteLocallyFreeModules_iff F :
    IsCrystalInFiniteLocallyFreeModules F ↔
      IsCrystalInQuasiCoherentModules F ∧ F.IsFiniteLocallyFree)

end

section

variable {S : Scheme.{u}} {I : S.IdealSheafData}
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
variable (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))

/- Definition 60.11.3 (4) -/
@[stacks 07IU]
#check (SheafOfModules.isCrystalInFiniteLocallyFreeModules_iff F :
    IsCrystalInFiniteLocallyFreeModules F ↔
      IsCrystalInQuasiCoherentModules F ∧ F.IsFiniteLocallyFree)

end

