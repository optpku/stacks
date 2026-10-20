module

public import stacks_project.Chap60.Remark_60_13_2_Algebra
public import stacks_project.Chap60.Remark_60_13_2_Crystalline
public import stacks_project.Chap60.Remark_60_13_1
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CrystallineObject
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

namespace CrystallineObject.SecondOrderThickening

/-- Remark 60.13.2 (1): the explicit object `(U, T'', δ'')` of `Cris(X/S)` whose structure
sheaf is `𝒪_T ⊕ Ω[T/S] ⊕ Ω[T/S] ⊕ ⋀² Ω[T/S]`. -/
@[stacks 07J3]
def object
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallCrystallineSite S I γ h_compatible X x₀ :=
  smallObject I γ h_compatible x₀ T

/-- Remark 60.13.2 (2): the crystalline morphism induced by `q₀(f) = (f, 0, 0, 0)`. -/
@[stacks 07J3]
def q₀
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    object I γ h_compatible x₀ T ⟶ T :=
  q0Morph I γ h_compatible x₀ T

/-- Remark 60.13.2 (3): the crystalline morphism induced by `q₁(f) = (f, d[T/S](f), 0, 0)`. -/
@[stacks 07J3]
def q₁
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    object I γ h_compatible x₀ T ⟶ T :=
  q1Morph I γ h_compatible x₀ T

/-- Remark 60.13.2 (4): the crystalline morphism induced by
`q₂(f) = (f, d[T/S](f), d[T/S](f), 0)`. -/
@[stacks 07J3]
def q₂
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    object I γ h_compatible x₀ T ⟶ T :=
  q2Morph I γ h_compatible x₀ T

/-- Remark 60.13.2 (5): the crystalline morphism induced by `q₀₁(f, ω) = (f, ω, 0, 0)`. -/
@[stacks 07J3]
def q₀₁
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    object I γ h_compatible x₀ T ⟶ FirstOrderThickening.object I γ h_compatible x₀ T :=
  q01Morph I γ h_compatible x₀ T

/-- Remark 60.13.2 (6): the crystalline morphism induced by
`q₁₂(f, ω) = (f, d[T/S](f), ω, d ω)`. -/
@[stacks 07J3]
def q₁₂
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    object I γ h_compatible x₀ T ⟶ FirstOrderThickening.object I γ h_compatible x₀ T :=
  q12Morph I γ h_compatible x₀ T

/-- Remark 60.13.2 (7): the crystalline morphism induced by `q₀₂(f, ω) = (f, ω, ω, 0)`. -/
@[stacks 07J3]
def q₀₂
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    object I γ h_compatible x₀ T ⟶ FirstOrderThickening.object I γ h_compatible x₀ T :=
  q02Morph I γ h_compatible x₀ T

/-- Remark 60.13.2 (8): `q₀` is compatible with the divided powers on `J` and `J''`. -/
@[stacks 07J3]
theorem q0_isDPMorphism
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : T.obj.1.thickening.affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q0Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism (dividedPowers T W)
        ((q0Scheme T).appLE V W hVW).hom := sorry

/-- Remark 60.13.2 (9): `q₁` is compatible with the divided powers on `J` and `J''`. -/
@[stacks 07J3]
theorem q1_isDPMorphism
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : T.obj.1.thickening.affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q1Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism (dividedPowers T W)
        ((q1Scheme T).appLE V W hVW).hom := sorry

/-- Remark 60.13.2 (10): `q₂` is compatible with the divided powers on `J` and `J''`. -/
@[stacks 07J3]
theorem q2_isDPMorphism
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : T.obj.1.thickening.affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q2Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism (dividedPowers T W)
        ((q2Scheme T).appLE V W hVW).hom := sorry

/-- Remark 60.13.2 (11): `q₀₁` is compatible with the divided powers on `J'` and `J''`. -/
@[stacks 07J3]
theorem q01_isDPMorphism
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : (FirstOrderThickening.scheme T).affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q01Scheme T ⁻¹ᵁ V.1),
      (FirstOrderThickening.dividedPowers T V).IsDPMorphism (dividedPowers T W)
        ((q01Scheme T).appLE V W hVW).hom := sorry

/-- Remark 60.13.2 (12): `q₁₂` is compatible with the divided powers on `J'` and `J''`. -/
@[stacks 07J3]
theorem q12_isDPMorphism
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : (FirstOrderThickening.scheme T).affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q12Scheme T ⁻¹ᵁ V.1),
      (FirstOrderThickening.dividedPowers T V).IsDPMorphism (dividedPowers T W)
        ((q12Scheme T).appLE V W hVW).hom := sorry

/-- Remark 60.13.2 (13): `q₀₂` is compatible with the divided powers on `J'` and `J''`. -/
@[stacks 07J3]
theorem q02_isDPMorphism
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : (FirstOrderThickening.scheme T).affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q02Scheme T ⁻¹ᵁ V.1),
      (FirstOrderThickening.dividedPowers T V).IsDPMorphism (dividedPowers T W)
        ((q02Scheme T).appLE V W hVW).hom := sorry

/-- Remark 60.13.2 (14): `q₀ = q₀₁ ∘ p₀`. -/
@[stacks 07J3]
theorem q0_eq_q01_comp_p0
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    q₀₁ I γ h_compatible x₀ T ≫ FirstOrderThickening.p₀ I γ h_compatible x₀ T =
      q₀ I γ h_compatible x₀ T := sorry

/-- Remark 60.13.2 (15): `q₁ = q₀₁ ∘ p₁`. -/
@[stacks 07J3]
theorem q1_eq_q01_comp_p1
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    q₀₁ I γ h_compatible x₀ T ≫ FirstOrderThickening.p₁ I γ h_compatible x₀ T =
      q₁ I γ h_compatible x₀ T := sorry

/-- Remark 60.13.2 (16): `q₁ = q₁₂ ∘ p₀`. -/
@[stacks 07J3]
theorem q1_eq_q12_comp_p0
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    q₁₂ I γ h_compatible x₀ T ≫ FirstOrderThickening.p₀ I γ h_compatible x₀ T =
      q₁ I γ h_compatible x₀ T := sorry

/-- Remark 60.13.2 (17): `q₂ = q₁₂ ∘ p₁`. -/
@[stacks 07J3]
theorem q2_eq_q12_comp_p1
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    q₁₂ I γ h_compatible x₀ T ≫ FirstOrderThickening.p₁ I γ h_compatible x₀ T =
      q₂ I γ h_compatible x₀ T := sorry

/-- Remark 60.13.2 (18): `q₀ = q₀₂ ∘ p₀`. -/
@[stacks 07J3]
theorem q0_eq_q02_comp_p0
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    q₀₂ I γ h_compatible x₀ T ≫ FirstOrderThickening.p₀ I γ h_compatible x₀ T =
      q₀ I γ h_compatible x₀ T := sorry

/-- Remark 60.13.2 (19): `q₂ = q₀₂ ∘ p₁`. -/
@[stacks 07J3]
theorem q2_eq_q02_comp_p1
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    q₀₂ I γ h_compatible x₀ T ≫ FirstOrderThickening.p₁ I γ h_compatible x₀ T =
      q₂ I γ h_compatible x₀ T := sorry

end CrystallineObject.SecondOrderThickening
