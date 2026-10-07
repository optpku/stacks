module

public import stacks_project.Chap60.Lemma_60_11_2_Restriction

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf

@[expose] public section

universe u

/-- Lemma 60.11.2 (1): with the crystalline site notation of Definition 60.11.1,
a sheaf of modules on `CRIS(X/S)` is quasi-coherent if and only if it is locally
quasi-coherent and a crystal in `𝒪_{X/S}`-modules. -/
@[stacks 07IT]
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
    {𝒪 : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) :
    F.IsQuasicoherent ↔
      IsLocallyQuasiCoherent (restrict F) ∧ IsCrystal (restrict F) := sorry

/-- Lemma 60.11.2 (2): with the crystalline site notation of Definition 60.11.1,
a sheaf of modules on `Cris(X/S)` is quasi-coherent if and only if it is locally
quasi-coherent and a crystal in `𝒪_{X/S}`-modules. -/
@[stacks 07IT]
theorem CrisModuleSheaf.isQuasiCoherent_iff_isLocallyQuasiCoherent_and_isCrystal
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
    F.IsQuasicoherent ↔
      CrisModuleSheaf.IsLocallyQuasiCoherent (CrisModuleSheaf.restrict F) ∧
        CrisModuleSheaf.IsCrystal (CrisModuleSheaf.restrict F) := sorry

end
