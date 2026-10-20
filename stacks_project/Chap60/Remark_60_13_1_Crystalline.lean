module

public import stacks_project.Chap60.Remark_60_13_1_SquareZero
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.IsFirstOrderThickening
open CrystallineObject
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.SquareZeroExtension
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

namespace CrystallineObject.FirstOrderThickening


/-- An affine open of the square-zero scheme is affine in the base scheme on the same
underlying open. -/
theorem baseOpen_isAffine
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    (V.1 : T.obj.1.thickening.Opens) ∈ T.obj.1.thickening.affineOpens := sorry

/-- The affine open of `T` underlying an affine open of the square-zero scheme. -/
def baseAffineOpen
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) : T.obj.1.thickening.affineOpens :=
  ⟨V.1, baseOpen_isAffine T V⟩

/-- The canonical module structure of `Ω[T/S]` on a square-zero affine open. -/
abbrev differentialModule
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    Module Γ(T.obj.1.thickening, baseAffineOpen T V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1)) :=
  (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1) |>.isModule

set_option backward.isDefEq.respectTransparency false in
/-- The affine-section ideal `J ⊕ Ω` in the square-zero extension. -/
def idealFamily
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    Ideal Γ(scheme T, V) :=
  -- Local instance justification (instance diamond): canonical affine-section module action.
  letI : Module Γ(T.obj.1.thickening, baseAffineOpen T V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1)) :=
    differentialModule T V
  -- Local instance justification (instance diamond): induced affine opposite action.
  letI : Module Γ(T.obj.1.thickening, baseAffineOpen T V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1)) :=
    oppositeModule _ _
  -- Local instance justification (proof-local temporary data): affine centrality law.
  letI : IsCentralScalar Γ(T.obj.1.thickening, baseAffineOpen T V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1)) :=
    oppositeModule_isCentral _ _
  @DividedPowers.TrivSqZeroExt.ideal
    Γ(T.obj.1.thickening, baseAffineOpen T V)
    inferInstance
    ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1))
    inferInstance (differentialModule T V)
    (oppositeModule _ _) (oppositeModule_isCentral _ _)
    (T.obj.1.ideal.ideal (baseAffineOpen T V))

/-- The family `J ⊕ Ω` is compatible with localization on affine basic opens. -/
theorem idealFamily_map_basicOpen
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (f : Γ(scheme T, V)) :
    (idealFamily T V).map
        ((scheme T).presheaf.map
          (homOfLE ((scheme T).basicOpen_le f)).op).hom =
      idealFamily T ((scheme T).affineBasicOpen f) := sorry

/-- The ideal sheaf `J' = J ⊕ Ω` on the explicit square-zero scheme. -/
def ideal
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (scheme T).IdealSheafData where
  ideal := idealFamily T
  map_ideal_basicOpen := idealFamily_map_basicOpen T

set_option backward.isDefEq.respectTransparency false in
/-- The explicit divided powers on `J' = J ⊕ Ω`. -/
def dividedPowers
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    DividedPowers ((ideal T).ideal V) :=
  -- Local instance justification (instance diamond): canonical affine-section module action.
  letI : Module Γ(T.obj.1.thickening, baseAffineOpen T V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1)) :=
    differentialModule T V
  -- Local instance justification (instance diamond): induced affine opposite action.
  letI : Module Γ(T.obj.1.thickening, baseAffineOpen T V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1)) :=
    oppositeModule _ _
  -- Local instance justification (proof-local temporary data): affine centrality law.
  letI : IsCentralScalar Γ(T.obj.1.thickening, baseAffineOpen T V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1)) :=
    oppositeModule_isCentral _ _
  @DividedPowers.TrivSqZeroExt.dividedPowers
    Γ(T.obj.1.thickening, baseAffineOpen T V)
    inferInstance
    ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1))
    inferInstance (differentialModule T V)
    (oppositeModule _ _) (oppositeModule_isCentral _ _)
    (T.obj.1.ideal.ideal (baseAffineOpen T V))
    (T.obj.1.gamma (baseAffineOpen T V))

/-- The explicit divided powers commute with restriction to affine basic opens. -/
theorem dividedPowers_compatible
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : (scheme T).affineOpens)
      (f : Γ(scheme T, V)),
      (dividedPowers T V).IsDPMorphism
        (dividedPowers T ((scheme T).affineBasicOpen f))
        ((scheme T).presheaf.map
          (homOfLE ((scheme T).basicOpen_le f)).op).hom := sorry

/-- The ideal `J ⊕ Ω` defines a divided-power thickening. -/
theorem isDividedPowerThickening
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    IsDividedPowerThickening (scheme T) (ideal T)
      (dividedPowers T) (dividedPowers_compatible T) := sorry

/-- The source inclusion commutes with the structure morphism to `S`. -/
theorem source_comm
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T.obj.1.inclusion ≫ schemeInclusion T ≫
        (p₀Scheme T ≫ T.obj.1.thickeningToBase) =
      T.obj.1.source.hom ≫ x₀ ≫ I.subschemeι := sorry

/-- The source inclusion into the square-zero extension is a genuine
thickening and its kernel is the displayed divided-power ideal. -/
theorem inclusion_spec
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    IsThickening (T.obj.1.inclusion ≫ schemeInclusion T) ∧
      ideal T = (T.obj.1.inclusion ≫ schemeInclusion T).ker := sorry

/-- The crystalline object carried by the explicit square-zero extension. -/
def crystallineObject
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CRIS S I γ h_compatible X x₀ :=
  CrystallineObject.of I γ h_compatible X x₀ T.obj.1.source
    (scheme T) (p₀Scheme T ≫ T.obj.1.thickeningToBase)
    (T.obj.1.inclusion ≫ schemeInclusion T) (ideal T)
    (dividedPowers T) (dividedPowers_compatible T)
    (isDividedPowerThickening T) (inclusion_spec T).1 (inclusion_spec T).2 (source_comm T)

/-- The explicit square-zero crystalline object is compatible with the divided powers on
the base scheme. -/
theorem crystallineObject_baseCompatible
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrystallineBaseCompatible I γ h_compatible x₀
      (crystallineObject I γ h_compatible x₀ T) := sorry

/-- The explicit square-zero construction as an object of the relative crystalline
category. -/
def relativeObject
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    RelativeCRIS S I γ h_compatible X x₀ :=
  ⟨crystallineObject I γ h_compatible x₀ T,
    crystallineObject_baseCompatible I γ h_compatible x₀ T⟩

/-- The source of the explicit square-zero object remains the original open subscheme of
`X`. -/
theorem relativeObject_sourceIsOpen
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    IsOpenImmersion (relativeObject I γ h_compatible x₀ T).1.source.hom := sorry

/-- The explicit square-zero crystalline object in the full small crystalline site. -/
def smallObject
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallCrystallineSite S I γ h_compatible X x₀ :=
  ⟨relativeObject I γ h_compatible x₀ T,
    relativeObject_sourceIsOpen I γ h_compatible x₀ T⟩

/-- The source square for the canonical inclusion commutes. -/
theorem inclusion_source_comm
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (𝟙 T.obj.1.source : T.obj.1.source ⟶ T.obj.1.source).left ≫
        (crystallineObject I γ h_compatible x₀ T).inclusion =
      T.obj.1.inclusion ≫ schemeInclusion T := sorry

/-- The canonical inclusion commutes with the structure morphisms to `S`. -/
theorem inclusion_base_comm
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    schemeInclusion T ≫
        (crystallineObject I γ h_compatible x₀ T).thickeningToBase =
      T.obj.1.thickeningToBase := sorry

/-- Pulling back `J ⊕ Ω` along the canonical inclusion lands in `J`. -/
theorem inclusion_ideal_compatible
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (crystallineObject I γ h_compatible x₀ T).ideal.comap
        (schemeInclusion T) ≤ T.obj.1.ideal := sorry

/-- The canonical inclusion preserves divided powers. -/
theorem inclusion_dividedPowers_compatible
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : (scheme T).affineOpens)
      (W : T.obj.1.thickening.affineOpens)
      (hVW : W.1 ≤ schemeInclusion T ⁻¹ᵁ V.1),
      ((crystallineObject I γ h_compatible x₀ T).gamma V).IsDPMorphism
        (T.obj.1.gamma W) ((schemeInclusion T).appLE V W hVW).hom := sorry

/-- The crystalline morphism underlying the canonical inclusion `T ⟶ T'`. -/
def inclusionHom
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrystallineObject.Hom T.obj.1
      (smallObject I γ h_compatible x₀ T).obj.1 where
  source := 𝟙 T.obj.1.source
  thickening := schemeInclusion T
  source_comm := inclusion_source_comm I γ h_compatible x₀ T
  base_comm := inclusion_base_comm I γ h_compatible x₀ T
  ideal_compatible := inclusion_ideal_compatible I γ h_compatible x₀ T
  dividedPowers_compatible :=
    inclusion_dividedPowers_compatible I γ h_compatible x₀ T

/-- The source square for the zero-section retraction commutes. -/
theorem p₀_source_comm
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (𝟙 T.obj.1.source : T.obj.1.source ⟶ T.obj.1.source).left ≫ T.obj.1.inclusion =
      (crystallineObject I γ h_compatible x₀ T).inclusion ≫
        p₀Scheme T := sorry

/-- The zero-section retraction commutes with the structure morphisms to `S`. -/
theorem p₀_base_comm
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    p₀Scheme T ≫ T.obj.1.thickeningToBase =
      (crystallineObject I γ h_compatible x₀ T).thickeningToBase := sorry

/-- Pulling `J` back along the zero-section retraction lands in `J ⊕ Ω`. -/
theorem p₀_ideal_compatible
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T.obj.1.ideal.comap (p₀Scheme T) ≤
      (crystallineObject I γ h_compatible x₀ T).ideal := sorry

/-- The zero-section retraction preserves divided powers. -/
theorem p₀_dividedPowers_compatible
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : T.obj.1.thickening.affineOpens)
      (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ p₀Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism
        ((crystallineObject I γ h_compatible x₀ T).gamma W)
        ((p₀Scheme T).appLE V W hVW).hom := sorry

/-- The crystalline morphism underlying the zero-section retraction `p₀ : T' ⟶ T`. -/
def p₀Hom
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrystallineObject.Hom
      (smallObject I γ h_compatible x₀ T).obj.1 T.obj.1 where
  source := 𝟙 T.obj.1.source
  thickening := p₀Scheme T
  source_comm := p₀_source_comm I γ h_compatible x₀ T
  base_comm := p₀_base_comm I γ h_compatible x₀ T
  ideal_compatible := p₀_ideal_compatible I γ h_compatible x₀ T
  dividedPowers_compatible := p₀_dividedPowers_compatible I γ h_compatible x₀ T

/-- The source square for the universal-differential retraction commutes. -/
theorem p₁_source_comm
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (𝟙 T.obj.1.source : T.obj.1.source ⟶ T.obj.1.source).left ≫ T.obj.1.inclusion =
      (crystallineObject I γ h_compatible x₀ T).inclusion ≫
        p₁Scheme T := sorry

/-- The universal-differential retraction commutes with the structure morphisms to `S`. -/
theorem p₁_base_comm
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    p₁Scheme T ≫ T.obj.1.thickeningToBase =
      (crystallineObject I γ h_compatible x₀ T).thickeningToBase := sorry

/-- Pulling `J` back along the universal-differential retraction lands in `J ⊕ Ω`. -/
theorem p₁_ideal_compatible
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T.obj.1.ideal.comap (p₁Scheme T) ≤
      (crystallineObject I γ h_compatible x₀ T).ideal := sorry

/-- The universal-differential retraction preserves divided powers. -/
theorem p₁_dividedPowers_compatible
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : T.obj.1.thickening.affineOpens)
      (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ p₁Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism
        ((crystallineObject I γ h_compatible x₀ T).gamma W)
        ((p₁Scheme T).appLE V W hVW).hom := sorry

/-- The crystalline morphism underlying the universal-differential retraction
`p₁ : T' ⟶ T`. -/
def p₁Hom
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrystallineObject.Hom
      (smallObject I γ h_compatible x₀ T).obj.1 T.obj.1 where
  source := 𝟙 T.obj.1.source
  thickening := p₁Scheme T
  source_comm := p₁_source_comm I γ h_compatible x₀ T
  base_comm := p₁_base_comm I γ h_compatible x₀ T
  ideal_compatible := p₁_ideal_compatible I γ h_compatible x₀ T
  dividedPowers_compatible := p₁_dividedPowers_compatible I γ h_compatible x₀ T

/-- The canonical inclusion as a morphism in the small crystalline site. -/
def inclusionMorph
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T ⟶ smallObject I γ h_compatible x₀ T :=
  ObjectProperty.homMk (inclusionHom I γ h_compatible x₀ T)

/-- The canonical zero-section retraction as a morphism in the small crystalline site. -/
def p₀Morph
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallObject I γ h_compatible x₀ T ⟶ T :=
  ObjectProperty.homMk (p₀Hom I γ h_compatible x₀ T)

/-- The canonical universal-differential retraction as a morphism in the small
crystalline site. -/
def p₁Morph
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallObject I γ h_compatible x₀ T ⟶ T :=
  ObjectProperty.homMk (p₁Hom I γ h_compatible x₀ T)



/-- The second coordinate `δ (n-1)(f) • ω` in the square-zero divided powers. -/
def dividedPowerSecondCoordinate
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (f : Γ(T.obj.1.thickening, baseAffineOpen T V))
    (ω : (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1)) :
    (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1) :=
  -- Local instance justification (defeq pin): action used by this square-zero divided power.
  letI : Module Γ(T.obj.1.thickening, baseAffineOpen T V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1)) :=
    differentialModule T V
  DividedPowers.TrivSqZeroExt.dpowPred
    (T.obj.1.gamma (baseAffineOpen T V)) n f • ω

/-- The divided powers on `J ⊕ Ω` satisfy `δ' n (f, ω) = (δ n f, δ (n-1) f • ω)`. -/
theorem dividedPowers_apply
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (z : (ideal T).ideal V) :
    (dividedPowers T V).dpow n z.1 =
      ((T.obj.1.gamma (baseAffineOpen T V)).dpow n z.1.1,
        dividedPowerSecondCoordinate h_compatible T V n z.1.1 z.1.2) := sorry

end CrystallineObject.FirstOrderThickening
