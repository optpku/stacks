module

public import stacks_project.Chap60.Remark_60_13_1_SquareZero
public import stacks_project.Chap60.Remark_60_13_1_Crystalline
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.IsFirstOrderThickening
open CrystallineObject
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

namespace CrystallineObject.FirstOrderThickening

/-- Remark 60.13.1 (1): the explicit object `(U, T', δ')` of `Cris(X/S)` whose structure
sheaf is `𝒪_T ⊕ Ω[T/S]` with square-zero multiplication. -/
@[stacks 07J2]
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

/-- Remark 60.13.1 (2): the crystalline inclusion `i : T ⟶ T'`. -/
@[stacks 07J2]
def inclusion
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T ⟶ object I γ h_compatible x₀ T :=
  inclusionMorph I γ h_compatible x₀ T

/-- Remark 60.13.1 (3): the crystalline retraction induced by `f ↦ (f, 0)`. -/
@[stacks 07J2]
def p₀
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    object I γ h_compatible x₀ T ⟶ T :=
  p₀Morph I γ h_compatible x₀ T

/-- Remark 60.13.1 (4): the crystalline retraction induced by `f ↦ (f, d[T/S](f))`. -/
@[stacks 07J2]
def p₁
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    object I γ h_compatible x₀ T ⟶ T :=
  p₁Morph I γ h_compatible x₀ T

/-- Remark 60.13.1 (5): the inclusion `i` is a first-order thickening. -/
@[stacks 07J2]
theorem isFirstOrder
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    IsFirstOrderThickening (inclusion I γ h_compatible x₀ T).hom.thickening := sorry

/-- Remark 60.13.1 (6): the ideal sheaf of `i` is identified with `Ω[T/S]`, equivalently
the inverse image `(Ω[X/S])_T` of Lemma 60.12.3. -/
@[stacks 07J2]
theorem ideal_eq
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ)
    (z : (sheaf T).obj.obj V) :
    z ∈ KernelIdeal.sectionIdeal (projection T) V ↔ z.1 = 0 := sorry

/-- Remark 60.13.1 (7): `p₁ - p₀` is the universal derivation `d[T/S]` composed with
the inclusion of `Ω[T/S]` as the square-zero ideal in `𝒪_T'`. -/
@[stacks 07J2]
theorem p₁_sub_p₀
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ)
    (f : T.obj.1.thickening.presheaf.obj V) :
    (differentialLift T).hom.app V f - (zeroLift T).hom.app V f =
      (0, (d[T.obj.1.thickeningToBase.toShHom]).d f) := sorry

/-- Remark 60.13.1 (8): `p₀ ∘ i = id`. -/
@[stacks 07J2]
theorem p₀_comp_inclusion
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    inclusion I γ h_compatible x₀ T ≫ p₀ I γ h_compatible x₀ T = 𝟙 T := sorry

/-- Remark 60.13.1 (9): `p₁ ∘ i = id`. -/
@[stacks 07J2]
theorem p₁_comp_inclusion
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    inclusion I γ h_compatible x₀ T ≫ p₁ I γ h_compatible x₀ T = 𝟙 T := sorry

/-- Sections of `𝒪_T'` are pairs `(f, ω)` in the trivial square-zero extension. -/
theorem sheaf_apply
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ)
    (z : (sheaf T).obj.obj V) :
    z = (z.1, z.2) := sorry

/-- Membership in `J ⊕ Ω` is membership of the first coordinate in `J`. -/
theorem mem_ideal_iff
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (z : Γ(scheme T, V)) :
    z ∈ (ideal T).ideal V ↔
      z.1 ∈ T.obj.1.ideal.ideal (baseAffineOpen T V) := sorry

end CrystallineObject.FirstOrderThickening
