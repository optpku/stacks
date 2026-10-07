module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Basic
public import stacks_project.Chap60.«60_8_1_1»
public import stacks_project.Chap60.«60_9_1_1_Site»
public import ReasLib.RingTheory.Localization.AtPrime.Int
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory MorphismProperty

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Crystalline

/-- 60.9.1.1: The forgetful functor from `Cris(X/S)` to `X.smallZariskiSite` sends a
crystalline object `(U, T, δ)` to its open source object `U`. -/
@[stacks 07IH]
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
  map := @smallCrystallineSourceMap S I γ h_compatible X x₀
  map_id := sorry
  map_comp := sorry

/-- The forgetful crystalline functor sends an object to its chosen open source. -/
@[stacks 07IH]
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
@[stacks 07IH]
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

end Crystalline
end Scheme
end AlgebraicGeometry
