/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Definition_60_11_3_Crystal
public import stacks_project.Chap60.Lemma_60_11_2

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open SheafOfModules

@[expose] public section

universe u

/-- Definition 60.11.3 (1): a sheaf of modules on `CRIS(X/S)` is a crystal in
quasi-coherent modules if and only if it is quasi-coherent, equivalently locally
quasi-coherent and a crystal in `𝒪_{X/S}`-modules. -/
@[stacks 07IU]
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
    {𝒪 : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) :
    IsCrystalInQuasiCoherentModules F ↔
      F.IsQuasicoherent ∧
        IsLocallyQuasiCoherent (restrict F) ∧ IsCrystal (restrict F) := sorry

/-- Definition 60.11.3 (2): a sheaf of modules on `Cris(X/S)` is a crystal in
quasi-coherent modules if and only if it is quasi-coherent, equivalently locally
quasi-coherent and a crystal in `𝒪_{X/S}`-modules. -/
@[stacks 07IU]
theorem CrisModuleSheaf.isCrystalInQuasiCoherentModules_iff
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
    {𝒪 : Sheaf (@smallCrystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) :
    IsCrystalInQuasiCoherentModules F ↔
      F.IsQuasicoherent ∧
        CrisModuleSheaf.IsLocallyQuasiCoherent (CrisModuleSheaf.restrict F) ∧
          CrisModuleSheaf.IsCrystal (CrisModuleSheaf.restrict F) := sorry

/-- Definition 60.11.3 (3): a sheaf of modules on `CRIS(X/S)` is a crystal in finite
locally free modules if and only if it is a crystal in quasi-coherent modules and
finite locally free. -/
@[stacks 07IU]
theorem CrystallineModuleSheaf.isCrystalInFiniteLocallyFreeModules_iff
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
    {𝒪 : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) :
    IsCrystalInFiniteLocallyFreeModules F ↔
      IsCrystalInQuasiCoherentModules F ∧ F.IsFiniteLocallyFree := sorry

/-- Definition 60.11.3 (4): a sheaf of modules on `Cris(X/S)` is a crystal in finite
locally free modules if and only if it is a crystal in quasi-coherent modules and
finite locally free. -/
@[stacks 07IU]
theorem CrisModuleSheaf.isCrystalInFiniteLocallyFreeModules_iff
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
    {𝒪 : Sheaf (@smallCrystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) :
    IsCrystalInFiniteLocallyFreeModules F ↔
      IsCrystalInQuasiCoherentModules F ∧ F.IsFiniteLocallyFree := sorry

end
