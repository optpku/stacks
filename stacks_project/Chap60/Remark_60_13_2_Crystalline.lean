/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_13_2_Algebra
public import stacks_project.Chap60.Remark_60_13_1_Crystalline
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

/-- The scheme morphism `T'' ⟶ T` induced by a lift `𝒪_T ⟶ 𝒪_{T''}`. -/
def retraction
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (lift : T.obj.1.thickening.sheaf ⟶ sheaf T) :
    scheme T ⟶ T.obj.1.thickening :=
  ⟨{ toHom := { base := 𝟙 T.obj.1.thickening.toTopCat, c := lift.hom }
     prop := fun _ => sorry }⟩

/-- The scheme morphism `T'' ⟶ T'` induced by a lift `𝒪_{T'} ⟶ 𝒪_{T''}`. -/
def retractionFirstOrder
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (lift : FirstOrderThickening.sheaf T ⟶ sheaf T) :
    scheme T ⟶ FirstOrderThickening.scheme T :=
  ⟨{ toHom := { base := 𝟙 T.obj.1.thickening.toTopCat, c := lift.hom }
     prop := fun _ => sorry }⟩

/-- Scheme map `q₀ : T'' ⟶ T`. -/
def q0Scheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    scheme T ⟶ T.obj.1.thickening :=
  retraction T (q0 T)

/-- Scheme map `q₁ : T'' ⟶ T`. -/
def q1Scheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    scheme T ⟶ T.obj.1.thickening :=
  retraction T (q1 T)

/-- Scheme map `q₂ : T'' ⟶ T`. -/
def q2Scheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    scheme T ⟶ T.obj.1.thickening :=
  retraction T (q2 T)

/-- Scheme map `q₀₁ : T'' ⟶ T'`. -/
def q01Scheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    scheme T ⟶ FirstOrderThickening.scheme T :=
  retractionFirstOrder T (q01 T)

/-- Scheme map `q₁₂ : T'' ⟶ T'`. -/
def q12Scheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    scheme T ⟶ FirstOrderThickening.scheme T :=
  retractionFirstOrder T (q12 T)

/-- Scheme map `q₀₂ : T'' ⟶ T'`. -/
def q02Scheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    scheme T ⟶ FirstOrderThickening.scheme T :=
  retractionFirstOrder T (q02 T)

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
        (q0Scheme T ≫ T.obj.1.thickeningToBase) =
      T.obj.1.source.hom ≫ x₀ ≫ I.subschemeι := sorry

/-- The source inclusion into the second-order thickening is a genuine
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

/-- The crystalline object carried by the explicit second-order thickening. -/
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
    (scheme T) (q0Scheme T ≫ T.obj.1.thickeningToBase)
    (T.obj.1.inclusion ≫ schemeInclusion T)
    (ideal T) (dividedPowers T) (dividedPowers_compatible T)
    (isDividedPowerThickening T) (inclusion_spec T).1 (inclusion_spec T).2 (source_comm T)

/-- Base divided-power compatibility of the second-order object. -/
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

/-- The second-order object in the relative crystalline category. -/
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

/-- The source remains an open immersion. -/
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

/-- The second-order object of `Cris(X/S)`. -/
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

/-- Source square for `q₀`. -/
theorem q0_source_comm
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (𝟙 T.obj.1.source : T.obj.1.source ⟶ T.obj.1.source).left ≫ T.obj.1.inclusion =
      (crystallineObject I γ h_compatible x₀ T).inclusion ≫ q0Scheme T := sorry

/-- Base square for `q₀`. -/
theorem q0_base_comm
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    q0Scheme T ≫ T.obj.1.thickeningToBase =
      (crystallineObject I γ h_compatible x₀ T).thickeningToBase := sorry

/-- Ideal compatibility for `q₀`. -/
theorem q0_ideal_compatible
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T.obj.1.ideal.comap (q0Scheme T) ≤ (ideal T) := sorry

/-- Divided-power compatibility for `q₀`. -/
theorem q0_dividedPowers_compatible
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
      (T.obj.1.gamma V).IsDPMorphism
        ((crystallineObject I γ h_compatible x₀ T).gamma W)
        ((q0Scheme T).appLE V W hVW).hom := sorry

/-- Crystalline homomorphism underlying `q₀`. -/
def q0Hom
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrystallineObject.Hom (smallObject I γ h_compatible x₀ T).obj.1 T.obj.1 where
  source := 𝟙 T.obj.1.source
  thickening := q0Scheme T
  source_comm := q0_source_comm I γ h_compatible x₀ T
  base_comm := q0_base_comm I γ h_compatible x₀ T
  ideal_compatible := q0_ideal_compatible I γ h_compatible x₀ T
  dividedPowers_compatible := q0_dividedPowers_compatible I γ h_compatible x₀ T

/-- Crystalline homomorphism underlying `q₁`. -/
def q1Hom
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrystallineObject.Hom (smallObject I γ h_compatible x₀ T).obj.1 T.obj.1 where
  source := 𝟙 T.obj.1.source
  thickening := q1Scheme T
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- Crystalline homomorphism underlying `q₂`. -/
def q2Hom
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrystallineObject.Hom (smallObject I γ h_compatible x₀ T).obj.1 T.obj.1 where
  source := 𝟙 T.obj.1.source
  thickening := q2Scheme T
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- Crystalline homomorphism underlying `q₀₁`. -/
def q01Hom
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrystallineObject.Hom (smallObject I γ h_compatible x₀ T).obj.1
      (FirstOrderThickening.smallObject I γ h_compatible x₀ T).obj.1 where
  source := 𝟙 T.obj.1.source
  thickening := q01Scheme T
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- Crystalline homomorphism underlying `q₁₂`. -/
def q12Hom
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrystallineObject.Hom (smallObject I γ h_compatible x₀ T).obj.1
      (FirstOrderThickening.smallObject I γ h_compatible x₀ T).obj.1 where
  source := 𝟙 T.obj.1.source
  thickening := q12Scheme T
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- Crystalline homomorphism underlying `q₀₂`. -/
def q02Hom
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrystallineObject.Hom (smallObject I γ h_compatible x₀ T).obj.1
      (FirstOrderThickening.smallObject I γ h_compatible x₀ T).obj.1 where
  source := 𝟙 T.obj.1.source
  thickening := q02Scheme T
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- Small-site morphism `q₀ : T'' ⟶ T`. -/
def q0Morph
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallObject I γ h_compatible x₀ T ⟶ T :=
  ObjectProperty.homMk (q0Hom I γ h_compatible x₀ T)

/-- Small-site morphism `q₁ : T'' ⟶ T`. -/
def q1Morph
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallObject I γ h_compatible x₀ T ⟶ T :=
  ObjectProperty.homMk (q1Hom I γ h_compatible x₀ T)

/-- Small-site morphism `q₂ : T'' ⟶ T`. -/
def q2Morph
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallObject I γ h_compatible x₀ T ⟶ T :=
  ObjectProperty.homMk (q2Hom I γ h_compatible x₀ T)

/-- Small-site morphism `q₀₁ : T'' ⟶ T'`. -/
def q01Morph
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallObject I γ h_compatible x₀ T ⟶
      FirstOrderThickening.smallObject I γ h_compatible x₀ T :=
  ObjectProperty.homMk (q01Hom I γ h_compatible x₀ T)

/-- Small-site morphism `q₁₂ : T'' ⟶ T'`. -/
def q12Morph
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallObject I γ h_compatible x₀ T ⟶
      FirstOrderThickening.smallObject I γ h_compatible x₀ T :=
  ObjectProperty.homMk (q12Hom I γ h_compatible x₀ T)

/-- Small-site morphism `q₀₂ : T'' ⟶ T'`. -/
def q02Morph
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallObject I γ h_compatible x₀ T ⟶
      FirstOrderThickening.smallObject I γ h_compatible x₀ T :=
  ObjectProperty.homMk (q02Hom I γ h_compatible x₀ T)

end CrystallineObject.SecondOrderThickening
