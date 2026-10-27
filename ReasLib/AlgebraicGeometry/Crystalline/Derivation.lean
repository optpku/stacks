/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Module
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry RelativeDerivation

universe u

namespace CrystallineModuleSheaf

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
  /-- Components commute with the actual pullback comparison for relative differentials. -/
  natural : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (φ : CrystallineObject.Hom A B),
      (Scheme.Modules.pullback φ.thickening).map
          (RingedSpace.Hom.differentialDesc B.thickeningToBase.toShHom (component B)) ≫
        F.comparison φ =
      RingedSpace.Hom.Differentials.comparison
          (⟨by simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom,
              Category.comp_id] using
              congrArg (fun f : A.thickening ⟶ S => f.toLRSHom.toShHom) φ.base_comm⟩ :
            CommSq φ.thickening.toShHom A.thickeningToBase.toShHom
              B.thickeningToBase.toShHom (𝟙 S.toRingedSpace)) ≫
        RingedSpace.Hom.differentialDesc A.thickeningToBase.toShHom (component A)
  /-- Divided-power compatibility on every affine section. -/
  dividedPower : ∀ (T : CRIS S I γ h_compatible X x₀) (W : T.thickening.affineOpens)
      (n : ℕ+) {x : Γ(T.thickening, W)}, x ∈ T.ideal.ideal W →
      (component T).d ((T.gamma W).dpow (n : ℕ) x) =
        (T.gamma W).dpow ((n : ℕ) - 1) x • (component T).d x

/-- Construct an `S`-derivation from relative derivations, naturality, and the divided-power relation. -/
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
    (natural : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (φ : CrystallineObject.Hom A B),
      (Scheme.Modules.pullback φ.thickening).map
          (RingedSpace.Hom.differentialDesc B.thickeningToBase.toShHom (component B)) ≫
        F.comparison φ =
      RingedSpace.Hom.Differentials.comparison
          (⟨by simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom,
              Category.comp_id] using
              congrArg (fun f : A.thickening ⟶ S => f.toLRSHom.toShHom) φ.base_comm⟩ :
            CommSq φ.thickening.toShHom A.thickeningToBase.toShHom
              B.thickeningToBase.toShHom (𝟙 S.toRingedSpace)) ≫
        RingedSpace.Hom.differentialDesc A.thickeningToBase.toShHom (component A))
    (dividedPower : ∀ (T : CRIS S I γ h_compatible X x₀) (W : T.thickening.affineOpens)
      (n : ℕ+) {x : Γ(T.thickening, W)}, x ∈ T.ideal.ideal W →
      (component T).d ((T.gamma W).dpow (n : ℕ) x) =
        (T.gamma W).dpow ((n : ℕ) - 1) x • (component T).d x) :
    SDerivation p S I γ h_compatible s X x₀ h_p F :=
  { component, natural, dividedPower }

/-- The naturality and divided-power clauses of an `S`-derivation. -/
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
      (Scheme.Modules.pullback φ.thickening).map
          (RingedSpace.Hom.differentialDesc B.thickeningToBase.toShHom (D.component B)) ≫
        F.comparison φ =
      RingedSpace.Hom.Differentials.comparison
          (⟨by simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom,
              Category.comp_id] using
              congrArg (fun f : A.thickening ⟶ S => f.toLRSHom.toShHom) φ.base_comm⟩ :
            CommSq φ.thickening.toShHom A.thickeningToBase.toShHom
              B.thickeningToBase.toShHom (𝟙 S.toRingedSpace)) ≫
        RingedSpace.Hom.differentialDesc A.thickeningToBase.toShHom (D.component A)) ∧
      (∀ (T : CRIS S I γ h_compatible X x₀) (W : T.thickening.affineOpens)
        (n : ℕ+) {x : Γ(T.thickening, W)}, x ∈ T.ideal.ideal W →
        (D.component T).d ((T.gamma W).dpow (n : ℕ) x) =
          (T.gamma W).dpow ((n : ℕ) - 1) x • (D.component T).d x) := ⟨D.natural, D.dividedPower⟩

end CrystallineModuleSheaf

end
