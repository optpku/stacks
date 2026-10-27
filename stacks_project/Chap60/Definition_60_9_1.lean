/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Site


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/- Definition 60.9.1 (1): the small crystalline site consists of crystalline
objects whose source over `X` is an open immersion. -/
@[stacks 07IG] #check
  (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineSite S I γ h_compatible X x₀ : Type (u + 1))

/- Definition 60.9.1 (2) -/
@[stacks 07IG]
#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineTopology : ∀ (p : ℕ) [Fact (Nat.Prime p)] (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))),
    GrothendieckTopology (smallCrystallineSite S I γ h_compatible X x₀))

/- Definition 60.9.1 (3) -/
@[stacks 07IG]
#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineTopos p S I γ h_compatible s X x₀ h_p : Type (u + 2))

end AlgebraicGeometry.Scheme.Crystalline
