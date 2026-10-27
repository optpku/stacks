/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.SecondOrder
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineObject
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

noncomputable section

universe u

open CrystallineObject.DividedPowerSecondOrderThickening

/- Remark 60.13.2: The second-order crystalline thickening by divided-power relative
one-forms in two directions and their exterior two-forms. -/
@[stacks 07J3] #check (CrystallineObject.DividedPowerSecondOrderThickening.object :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  smallCrystallineSite S I γ h_compatible X x₀)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q₀ :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  object I γ h_compatible x₀ T ⟶ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q₁ :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  object I γ h_compatible x₀ T ⟶ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q₂ :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  object I γ h_compatible x₀ T ⟶ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q₀₁ :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  object I γ h_compatible x₀ T ⟶ DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q₁₂ :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  object I γ h_compatible x₀ T ⟶ DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q₀₂ :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  object I γ h_compatible x₀ T ⟶ DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q0_isDPMorphism :
  ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  ∀ (V : T.obj.1.thickening.affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q0Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism (dividedPowers T W)
        ((q0Scheme T).appLE V W hVW).hom)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q1_isDPMorphism :
  ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  ∀ (V : T.obj.1.thickening.affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q1Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism (dividedPowers T W)
        ((q1Scheme T).appLE V W hVW).hom)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q2_isDPMorphism :
  ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  ∀ (V : T.obj.1.thickening.affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q2Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism (dividedPowers T W)
        ((q2Scheme T).appLE V W hVW).hom)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q01_isDPMorphism :
  ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  ∀ (V : (DividedPowerFirstOrderThickening.scheme T).affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q01Scheme T ⁻¹ᵁ V.1),
      (DividedPowerFirstOrderThickening.dividedPowers T V).IsDPMorphism (dividedPowers T W)
        ((q01Scheme T).appLE V W hVW).hom)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q12_isDPMorphism :
  ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  ∀ (V : (DividedPowerFirstOrderThickening.scheme T).affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q12Scheme T ⁻¹ᵁ V.1),
      (DividedPowerFirstOrderThickening.dividedPowers T V).IsDPMorphism (dividedPowers T W)
        ((q12Scheme T).appLE V W hVW).hom)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q02_isDPMorphism :
  ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  ∀ (V : (DividedPowerFirstOrderThickening.scheme T).affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q02Scheme T ⁻¹ᵁ V.1),
      (DividedPowerFirstOrderThickening.dividedPowers T V).IsDPMorphism (dividedPowers T W)
        ((q02Scheme T).appLE V W hVW).hom)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q0_eq_q01_comp_p0 :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  q₀₁ I γ h_compatible x₀ T ≫ DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T =
      q₀ I γ h_compatible x₀ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q1_eq_q01_comp_p1 :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  q₀₁ I γ h_compatible x₀ T ≫ DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T =
      q₁ I γ h_compatible x₀ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q1_eq_q12_comp_p0 :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  q₁₂ I γ h_compatible x₀ T ≫ DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T =
      q₁ I γ h_compatible x₀ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q2_eq_q12_comp_p1 :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  q₁₂ I γ h_compatible x₀ T ≫ DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T =
      q₂ I γ h_compatible x₀ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q0_eq_q02_comp_p0 :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  q₀₂ I γ h_compatible x₀ T ≫ DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T =
      q₀ I γ h_compatible x₀ T)

#check (CrystallineObject.DividedPowerSecondOrderThickening.q2_eq_q02_comp_p1 :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
  q₀₂ I γ h_compatible x₀ T ≫ DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T =
      q₂ I γ h_compatible x₀ T)

#check (DividedPowers.SecondOrderDifferential.mul_apply :
  ∀ {A M N : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (w : M →ₗ[A] M →ₗ[A] N)
    (a b : A) (ω₁ ω₂ τ₁ τ₂ : M) (η θ : N),
    DividedPowers.SecondOrderDifferential.ofCoordinates w a ω₁ ω₂ η *
      DividedPowers.SecondOrderDifferential.ofCoordinates w b τ₁ τ₂ θ =
        DividedPowers.SecondOrderDifferential.ofCoordinates w (a * b)
          (a • τ₁ + b • ω₁) (a • τ₂ + b • ω₂)
          (a • θ + b • η + w ω₁ τ₂ + w τ₁ ω₂))

#check (DividedPowers.SecondOrderDifferential.dividedPowers_apply :
  ∀ {A M N : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (w : M →ₗ[A] M →ₗ[A] N)
    {J : Ideal A} (δ : DividedPowers J) (n : ℕ)
    (a : A), a ∈ J → ∀ (ω₁ ω₂ : M) (η : N),
    DividedPowers.SecondOrderDifferential.dividedPowers w δ n
      (DividedPowers.SecondOrderDifferential.ofCoordinates w a ω₁ ω₂ η) =
        DividedPowers.SecondOrderDifferential.ofCoordinates w (δ.dpow n a)
          (DividedPowers.BilinearExtension.dpowPred δ n a • ω₁)
          (DividedPowers.BilinearExtension.dpowPred δ n a • ω₂)
          (DividedPowers.BilinearExtension.dpowPred δ n a • η +
            DividedPowers.BilinearExtension.dpowPredTwo δ n a • w ω₁ ω₂))

