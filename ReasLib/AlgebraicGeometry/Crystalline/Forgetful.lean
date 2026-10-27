/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Site

@[expose] public section

open AlgebraicGeometry CategoryTheory MorphismProperty

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- The induced map of open sources preserves the identity of a small crystalline object. -/
theorem smallCrystallineSourceMap_id
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallCrystallineSourceMap S I γ h_compatible X x₀ (𝟙 T) =
      𝟙 (smallCrystallineSource S I γ h_compatible X x₀ T) := sorry

/-- The induced map of open sources preserves composition of small crystalline morphisms. -/
theorem smallCrystallineSourceMap_comp
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    {T U V : smallCrystallineSite S I γ h_compatible X x₀}
    (f : T ⟶ U) (g : U ⟶ V) :
    smallCrystallineSourceMap S I γ h_compatible X x₀ (f ≫ g) =
      smallCrystallineSourceMap S I γ h_compatible X x₀ f ≫
        smallCrystallineSourceMap S I γ h_compatible X x₀ g := sorry

/-- The forgetful functor from the small crystalline category to the small Zariski
category sends each divided-power thickening to its open source over `X`. -/
def forgetfulFunctor
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    smallCrystallineSite S I γ h_compatible X x₀ ⥤ X.smallZariskiSite where
  obj := smallCrystallineSource S I γ h_compatible X x₀
  map f := smallCrystallineSourceMap S I γ h_compatible X x₀ f
  map_id := smallCrystallineSourceMap_id S I γ h_compatible X x₀
  map_comp := smallCrystallineSourceMap_comp S I γ h_compatible X x₀

/-- The forgetful crystalline functor sends an object to its chosen open source. -/
theorem forgetfulFunctor_obj
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
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).obj T =
      smallCrystallineSource S I γ h_compatible X x₀ T := sorry

/-- The forgetful crystalline functor acts on a morphism by the induced map of open sources. -/
theorem forgetfulFunctor_map
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
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) :
    (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).map f =
      smallCrystallineSourceMap S I γ h_compatible X x₀ f := sorry


end AlgebraicGeometry.Scheme.Crystalline
