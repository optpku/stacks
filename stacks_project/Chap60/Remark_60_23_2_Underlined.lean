/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import stacks_project.Chap60.Definition_60_11_1_ModuleProperties

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf

noncomputable section

universe u

variable {S : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)

/-- Base-change comparison for the underlined module sheaf along a morphism of
small crystalline objects, assembled from the source/inclusion square. -/
def CrisModuleSheaf.underlinedComparison (M : X.Modules)
    {A B : smallCrystallineSite S I γ h_compatible X x₀} (φ : A ⟶ B) :
    (pullback φ.hom.thickening).obj
        ((pushforward B.obj.1.inclusion).obj ((pullback B.obj.1.source.hom).obj M)) ⟶
      (pushforward A.obj.1.inclusion).obj ((pullback A.obj.1.source.hom).obj M) :=
  let t := φ.hom.thickening
  let s := φ.hom.source.left
  let iA := A.obj.1.inclusion
  let iB := B.obj.1.inclusion
  let uB := B.obj.1.source.hom
  let N := (pullback uB).obj M
  let P := (pullback t).obj ((pushforward iB).obj N)
  (pullbackPushforwardAdjunction iA).unit.app P ≫
    (pushforward iA).map
      ((pullbackComp iA t).hom.app ((pushforward iB).obj N) ≫
        (pullbackCongr φ.hom.source_comm.symm).hom.app ((pushforward iB).obj N) ≫
        (pullbackComp s iB).inv.app ((pushforward iB).obj N) ≫
        (pullback s).map ((pullbackPushforwardAdjunction iB).counit.app N) ≫
        (pullbackComp s uB).hom.app M ≫
        (pullbackCongr (Over.w φ.hom.source)).hom.app M)

/-- The underlined crystalline module sheaf associated to an `𝒪_X`-module `M`,
sending a thickening `T` to `inclusion_*` of the pullback of `M` along the source. -/
def CrisModuleSheaf.underlined (M : X.Modules) :
    CrisModuleSheaf S I γ h_compatible X x₀ where
  obj T := (pushforward T.obj.1.inclusion).obj ((pullback T.obj.1.source.hom).obj M)
  comparison φ := CrisModuleSheaf.underlinedComparison I γ h_compatible x₀ M φ

/-- Evaluation of the underlined module sheaf on a small crystalline thickening. -/
theorem CrisModuleSheaf.underlined_obj (M : X.Modules)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (CrisModuleSheaf.underlined I γ h_compatible x₀ M).obj T =
      (pushforward T.obj.1.inclusion).obj ((pullback T.obj.1.source.hom).obj M) :=
  sorry

/-- The comparison of `CrisModuleSheaf.underlined` is the source/inclusion base change. -/
theorem CrisModuleSheaf.underlined_comparison (M : X.Modules)
    {A B : smallCrystallineSite S I γ h_compatible X x₀} (φ : A ⟶ B) :
    (CrisModuleSheaf.underlined I γ h_compatible x₀ M).comparison φ =
      CrisModuleSheaf.underlinedComparison I γ h_compatible x₀ M φ :=
  sorry

/-- The underlined sheaf of a quasi-coherent `𝒪_X`-module is locally quasi-coherent. -/
instance CrisModuleSheaf.underlined_isLocallyQuasiCoherent (M : X.Modules) [M.IsQuasicoherent] :
    ModuleSheaf.IsLocallyQuasiCoherent (CrisModuleSheaf.underlined I γ h_compatible x₀ M) :=
  sorry

end
