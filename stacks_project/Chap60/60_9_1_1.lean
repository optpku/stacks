/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Forgetful
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline

universe u

/- 60.9.1.1: The forgetful functor `Cris(X/S) ⥤ X.smallZariskiSite` sends
 each crystalline object `(U, T, δ)` to its open source `U`. -/
@[stacks 07IH] #check (AlgebraicGeometry.Scheme.Crystalline.forgetfulFunctor :
    ∀ (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))),
    smallCrystallineSite S I γ h_compatible X x₀ ⥤ X.smallZariskiSite)
