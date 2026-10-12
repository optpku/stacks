/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_24_10_Rlim_Restriction
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.CategoryTheory.InverseSystem.Sequential

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Crystalline

universe u v w

@[expose] public section

/-- Iterated restriction of `F` from cutoff `e₀` along successive `p`-power stages. -/
noncomputable def restrictToPPowerStageIter
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
    (e₀ n : ℕ) :
    PPowerStageModuleSheaf p I γ h_compatible X x₀ (e₀ + n) :=
  match n with
  | 0 => restrictToPPowerStage p F e₀
  | n + 1 => restrictPPowerStageSucc p (restrictToPPowerStageIter p F e₀ n)

/-- Iterated restriction at `n = 0` is restriction of `F` to `Cris(X / S_{e₀})`. -/
theorem restrictToPPowerStageIter_zero
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
    (e₀ : ℕ) :
    restrictToPPowerStageIter p F e₀ 0 = restrictToPPowerStage p F e₀ := sorry

/-- The `n`th object of the `p`-power crystalline `RΓ` tower after cutoff `e₀`. -/
noncomputable def pPowerStageRGammaObj
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
    {D : Type w} [Category.{v, w} D]
    (rGammaStage :
      ∀ e : ℕ, PPowerStageModuleSheaf p I γ h_compatible X x₀ e → D)
    (F : CrystallineModuleSheaf (Spec (.of A)) I γ h_compatible X x₀)
    (e₀ n : ℕ) : D :=
  rGammaStage (e₀ + n) (restrictToPPowerStageIter p F e₀ n)

/-- Stage objects of the tower are derived sections of the restricted sheaf `F_{e₀+n}`. -/
theorem pPowerStageRGammaObj_eq
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
    {D : Type w} [Category.{v, w} D]
    (rGammaStage :
      ∀ e : ℕ, PPowerStageModuleSheaf p I γ h_compatible X x₀ e → D)
    (F : CrystallineModuleSheaf (Spec (.of A)) I γ h_compatible X x₀)
    (e₀ n : ℕ) :
    pPowerStageRGammaObj p rGammaStage F e₀ n =
      rGammaStage (e₀ + n) (restrictToPPowerStageIter p F e₀ n) := sorry

/-- Transition maps of the `p`-power `RΓ` tower are `RΓ` applied to successor restriction. -/
noncomputable def pPowerStageRGammaMap
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
    {D : Type w} [Category.{v, w} D]
    (rGammaStage :
      ∀ e : ℕ, PPowerStageModuleSheaf p I γ h_compatible X x₀ e → D)
    (rGammaStageRestrict :
      ∀ (e : ℕ) (F_e : PPowerStageModuleSheaf p I γ h_compatible X x₀ e),
        rGammaStage (e + 1) (restrictPPowerStageSucc p F_e) ⟶ rGammaStage e F_e)
    (F : CrystallineModuleSheaf (Spec (.of A)) I γ h_compatible X x₀)
    (e₀ n : ℕ) :
    pPowerStageRGammaObj p rGammaStage F e₀ (n + 1) ⟶
      pPowerStageRGammaObj p rGammaStage F e₀ n :=
  rGammaStageRestrict (e₀ + n) (restrictToPPowerStageIter p F e₀ n)

/-- Sequential inverse system whose `n`th object is
`RΓ(Cris(X / S_{e₀+n}), F_{e₀+n})`, with transition maps the image under `RΓ`
of restriction along `Cris(X / S_{e+1}) ⊆ Cris(X / S_e)`. -/
noncomputable def pPowerStageRGammaSystem
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
    {D : Type w} [Category.{v, w} D]
    (rGammaStage :
      ∀ e : ℕ, PPowerStageModuleSheaf p I γ h_compatible X x₀ e → D)
    (rGammaStageRestrict :
      ∀ (e : ℕ) (F_e : PPowerStageModuleSheaf p I γ h_compatible X x₀ e),
        rGammaStage (e + 1) (restrictPPowerStageSucc p F_e) ⟶ rGammaStage e F_e)
    (F : CrystallineModuleSheaf (Spec (.of A)) I γ h_compatible X x₀)
    (e₀ : ℕ) :
    SequentialInverseSystem D :=
  Functor.ofOpSequence (pPowerStageRGammaMap p rGammaStage rGammaStageRestrict F e₀)

/-- The sequential object at index `n` is `RΓ` of the restricted sheaf at stage `e₀ + n`. -/
theorem pPowerStageRGammaSystem_obj
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
    {D : Type w} [Category.{v, w} D]
    (rGammaStage :
      ∀ e : ℕ, PPowerStageModuleSheaf p I γ h_compatible X x₀ e → D)
    (rGammaStageRestrict :
      ∀ (e : ℕ) (F_e : PPowerStageModuleSheaf p I γ h_compatible X x₀ e),
        rGammaStage (e + 1) (restrictPPowerStageSucc p F_e) ⟶ rGammaStage e F_e)
    (F : CrystallineModuleSheaf (Spec (.of A)) I γ h_compatible X x₀)
    (e₀ n : ℕ) :
    (pPowerStageRGammaSystem p rGammaStage rGammaStageRestrict F e₀).obj (op n) =
      rGammaStage (e₀ + n) (restrictToPPowerStageIter p F e₀ n) := sorry
