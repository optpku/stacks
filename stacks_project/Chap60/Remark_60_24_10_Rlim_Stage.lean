/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Situation_60_7_5
public import stacks_project.Chap60.«60_9_1_1_Site»
public import ReasLib.RingTheory.Localization.AtPrime.Int

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Crystalline

universe u

@[expose] public section

/-- The affine `p`-power thickening `S_e = Spec(A / ⟨p^e⟩)`. -/
noncomputable def pPowerStageScheme (A : Type u) [CommRing A] (p e : ℕ) : Scheme.{u} :=
  Spec (.of (A ⧸ Ideal.span {(p : A) ^ e}))

/-- The `p`-power stage scheme is `Spec` of the corresponding principal-power quotient. -/
theorem pPowerStageScheme_spec (A : Type u) [CommRing A] (p e : ℕ) :
    pPowerStageScheme A p e = Spec (.of (A ⧸ Ideal.span {(p : A) ^ e})) := sorry

/-- The canonical closed immersion `S_e ⟶ Spec A` induced by `A → A / ⟨p^e⟩`. -/
noncomputable def pPowerStageToBase (A : Type u) [CommRing A] (p e : ℕ) :
    pPowerStageScheme A p e ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {(p : A) ^ e})))

/-- The base morphism of a `p`-power stage is the `Spec` of the quotient map. -/
theorem pPowerStageToBase_eq (A : Type u) [CommRing A] (p e : ℕ) :
    pPowerStageToBase A p e =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {(p : A) ^ e}))) := sorry

/-- A crystalline object over `Spec A` factors through `Cris(X / S_e)` when its thickening
to the base factors through `S_e = pPowerStageScheme A p e`. -/
def FactorsThroughPPowerStage
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
    (e : ℕ) (c : CRIS (Spec (.of A)) I γ h_compatible X x₀) : Prop :=
  ∃ g : c.thickening ⟶ pPowerStageScheme A p e,
    c.thickeningToBase = g ≫ pPowerStageToBase A p e

/-- If a crystalline object factors through `S_{e+1}`, it factors through `S_e`. -/
theorem factorsThroughPPowerStage_of_succ
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
    {c : CRIS (Spec (.of A)) I γ h_compatible X x₀}
    (hc : FactorsThroughPPowerStage p (e + 1) c) :
    FactorsThroughPPowerStage p e c := sorry
