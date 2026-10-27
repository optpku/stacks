/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.ZariskiComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

universe u

section

variable {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

variable [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]

#check
  (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineToposMorphism_inverseImage
      S I γ h_compatible s X x₀ h_p :
    (smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).inverseImage =
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).sheafPullbackCocontinuous
        (Type (u + 1)) (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        X.smallZariskiTopology)

#check
  (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineToposMorphism_pushforward
      S I γ h_compatible s X x₀ h_p :
    (smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).pushforward =
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).sheafPushforwardCocontinuous
        (Type (u + 1)) (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        X.smallZariskiTopology)

end
