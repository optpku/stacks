module

public import stacks_project.Chap60.Remark_60_24_10_Rlim_Stage
public import stacks_project.Chap60.«60_10_0_2_ModuleSheaf»

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Crystalline

universe u

@[expose] public section

/-- An `O_{X/S_e}`-module, presented as the values of a crystalline module on the full
subcategory `Cris(X / S_e) ⊆ Cris(X / S)`. -/
structure PPowerStageModuleSheaf
    (p : ℕ) [Fact (Nat.Prime p)] {A : Type u} [CommRing A]
    [Algebra (Int.LocalizationAtPrime p) A]
    (I : (Spec (.of A)).IdealSheafData)
    (γ : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γ V).IsDPMorphism (γ ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) (e : ℕ) where
  /-- The module sheaf on a crystalline object factoring through `S_e`. -/
  obj : ∀ (c : CRIS (Spec (.of A)) I γ h_compatible X x₀),
    FactorsThroughPPowerStage p e c → c.thickening.Modules
  /-- Comparison morphisms for maps of crystalline objects over `S_e`. -/
  comparison : ∀ {c d : CRIS (Spec (.of A)) I γ h_compatible X x₀}
      (f : CrystallineObject.Hom c d)
      (hd : FactorsThroughPPowerStage p e d) (hc : FactorsThroughPPowerStage p e c),
    (Scheme.Modules.pullback f.thickening).obj (obj d hd) ⟶ obj c hc

/-- Restriction of an `O_{X/S}`-module `F` to `Cris(X / S_e)`. -/
noncomputable def restrictToPPowerStage
    (p : ℕ) [Fact (Nat.Prime p)] {A : Type u} [CommRing A]
    [Algebra (Int.LocalizationAtPrime p) A]
    {I : (Spec (.of A)).IdealSheafData}
    {γ : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γ V).IsDPMorphism (γ ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineModuleSheaf (Spec (.of A)) I γ h_compatible X x₀)
    (e : ℕ) :
    PPowerStageModuleSheaf p I γ h_compatible X x₀ e where
  obj c _ := F.obj c
  comparison f _ _ := F.comparison f

/-- Restriction to `Cris(X / S_e)` evaluates the ambient sheaf on objects over `S_e`. -/
theorem restrictToPPowerStage_obj
    (p : ℕ) [Fact (Nat.Prime p)] {A : Type u} [CommRing A]
    [Algebra (Int.LocalizationAtPrime p) A]
    {I : (Spec (.of A)).IdealSheafData}
    {γ : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γ V).IsDPMorphism (γ ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineModuleSheaf (Spec (.of A)) I γ h_compatible X x₀)
    (e : ℕ) (c : CRIS (Spec (.of A)) I γ h_compatible X x₀)
    (hc : FactorsThroughPPowerStage p e c) :
    (restrictToPPowerStage p F e).obj c hc = F.obj c := sorry

/-- Further restriction along `Cris(X / S_{e+1}) ⊆ Cris(X / S_e)`. -/
noncomputable def restrictPPowerStageSucc
    (p : ℕ) [Fact (Nat.Prime p)] {A : Type u} [CommRing A]
    [Algebra (Int.LocalizationAtPrime p) A]
    {I : (Spec (.of A)).IdealSheafData}
    {γ : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γ V).IsDPMorphism (γ ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme} {e : ℕ}
    (F_e : PPowerStageModuleSheaf p I γ h_compatible X x₀ e) :
    PPowerStageModuleSheaf p I γ h_compatible X x₀ (e + 1) where
  obj c hc := F_e.obj c (factorsThroughPPowerStage_of_succ p hc)
  comparison f hd hc := F_e.comparison f
    (factorsThroughPPowerStage_of_succ p hd) (factorsThroughPPowerStage_of_succ p hc)

/-- Restricting `F_e` further along the successor stage recovers `F_{e+1}`. -/
theorem restrictPPowerStageSucc_eq
    (p : ℕ) [Fact (Nat.Prime p)] {A : Type u} [CommRing A]
    [Algebra (Int.LocalizationAtPrime p) A]
    {I : (Spec (.of A)).IdealSheafData}
    {γ : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γ V).IsDPMorphism (γ ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineModuleSheaf (Spec (.of A)) I γ h_compatible X x₀) (e : ℕ) :
    restrictPPowerStageSucc p (restrictToPPowerStage p F e) =
      restrictToPPowerStage p F (e + 1) := sorry
