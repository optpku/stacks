/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Definition_60_6_1
public import stacks_project.Chap60.«60_8_1_2_CrystallineObject»
public import stacks_project.Chap60.«60_10_0_2_ModuleSheaf»
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.RingTheory.Localization.AtPrime.Int
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory

universe u v

@[expose] public section

namespace CrystallineModuleSheaf

/-- A factorization of the whole thickening map through an open subscheme of `S`. -/
structure BaseOpenFactorization.{v_1}
    {S : Scheme.{v_1}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{v_1}} {x₀ : X ⟶ I.subscheme}
    (T : CRIS S I γ h_compatible X x₀) (V : S.Opens) where
  /-- The morphism from the thickening to the open subscheme. -/
  lift : T.thickening ⟶ V.toScheme
  /-- The factorization recovers the given morphism to `S`. -/
  fac : lift ≫ Scheme.Opens.ι V = T.thickeningToBase

/-- Construct a whole-thickening factorization through an open subscheme. -/
def BaseOpenFactorization.of
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {T : CRIS S I γ h_compatible X x₀} {V : S.Opens}
    (lift : T.thickening ⟶ V.toScheme)
    (fac : lift ≫ Scheme.Opens.ι V = T.thickeningToBase) :
    BaseOpenFactorization T V :=
  { lift, fac }

/-- An `S`-derivation on a crystalline object, transported along a crystalline
morphism through the source and target comparison morphisms of a module sheaf. -/
structure SDerivation.{u_1}
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u_1}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u_1} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u_1}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀) where
  /-- The actual sheaf-level relative derivation on every crystalline object. -/
  component : ∀ T : CRIS S I γ h_compatible X x₀,
    RingedSpace.Hom.derivations T.thickeningToBase.toShHom (F.obj T)
  /-- Pull a sheaf derivation across a crystalline morphism using its module comparison map. -/
  comparisonPullback :
    ∀ {A B : CRIS S I γ h_compatible X x₀}
      (φ : CrystallineObject.Hom A B)
      (c : (Scheme.Modules.pullback φ.thickening).obj (F.obj B) ⟶ F.obj A),
      RingedSpace.Hom.derivations B.thickeningToBase.toShHom (F.obj B) →
        RingedSpace.Hom.derivations A.thickeningToBase.toShHom (F.obj A)
  /-- The components are natural for every crystalline morphism through `F.comparison`. -/
  natural : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (φ : CrystallineObject.Hom A B),
      comparisonPullback φ (F.comparison φ) (component B) = component A
  /-- Divided-power compatibility on each affine section whenever the whole thickening
  factors through the chosen base open. -/
  dividedPower : ∀ (T : CRIS S I γ h_compatible X x₀) (V : S.Opens)
      (hV : BaseOpenFactorization T V) (W : T.thickening.affineOpens)
      (hWV : (W : T.thickening.Opens) ≤ T.thickeningToBase ⁻¹ᵁ V)
      (n : ℕ+) {x : Γ(T.thickening, W)}, x ∈ T.ideal.ideal W →
      (component T).d ((T.gamma W).dpow (n : ℕ) x) =
        (T.gamma W).dpow ((n : ℕ) - 1) x • (component T).d x

/-- Construct an `S`-derivation from its sheaf-level components, comparison transport,
naturality law, and divided-power compatibility. -/
def SDerivation.of
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
    (component : ∀ T : CRIS S I γ h_compatible X x₀,
      RingedSpace.Hom.derivations T.thickeningToBase.toShHom (F.obj T))
    (comparisonPullback :
      ∀ {A B : CRIS S I γ h_compatible X x₀}
        (φ : CrystallineObject.Hom A B)
        (c : (Scheme.Modules.pullback φ.thickening).obj (F.obj B) ⟶ F.obj A),
        RingedSpace.Hom.derivations B.thickeningToBase.toShHom (F.obj B) →
          RingedSpace.Hom.derivations A.thickeningToBase.toShHom (F.obj A))
    (natural : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (φ : CrystallineObject.Hom A B),
      comparisonPullback φ (F.comparison φ) (component B) = component A)
    (dividedPower : ∀ (T : CRIS S I γ h_compatible X x₀) (V : S.Opens)
      (hV : BaseOpenFactorization T V) (W : T.thickening.affineOpens)
      (hWV : (W : T.thickening.Opens) ≤ T.thickeningToBase ⁻¹ᵁ V)
      (n : ℕ+) {x : Γ(T.thickening, W)}, x ∈ T.ideal.ideal W →
      (component T).d ((T.gamma W).dpow (n : ℕ) x) =
        (T.gamma W).dpow ((n : ℕ) - 1) x • (component T).d x) :
    SDerivation p S I γ h_compatible s X x₀ h_p F :=
  { component, comparisonPullback, natural, dividedPower }

/-- The source-facing naturality and divided-power clauses of an `S`-derivation. -/
theorem SDerivation.spec
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
    (D : SDerivation p S I γ h_compatible s X x₀ h_p F) :
    (∀ {A B : CRIS S I γ h_compatible X x₀}
      (φ : CrystallineObject.Hom A B),
      D.comparisonPullback φ (F.comparison φ) (D.component B) = D.component A) ∧
      (∀ (T : CRIS S I γ h_compatible X x₀) (V : S.Opens)
        (hV : BaseOpenFactorization T V) (W : T.thickening.affineOpens)
        (hWV : (W : T.thickening.Opens) ≤ T.thickeningToBase ⁻¹ᵁ V)
        (n : ℕ+) {x : Γ(T.thickening, W)}, x ∈ T.ideal.ideal W →
        (D.component T).d ((T.gamma W).dpow (n : ℕ) x) =
          (T.gamma W).dpow ((n : ℕ) - 1) x • (D.component T).d x) := sorry

end CrystallineModuleSheaf

end
