/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Trivial.Small

import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Crystalline

/- 60.9.1.2: in Situation 60.7.5, the trivial crystalline functor
from `X.smallZariskiSite` to `smallCrystallineSite S I γ h_compatible X x₀`
sends an open object `U` to the identity thickening `(U, U, ∅)`. -/
@[stacks 07II] #check
  (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineTrivialFunctor :
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
    X.smallZariskiSite ⥤ smallCrystallineSite S I γ h_compatible X x₀)

/- The object of the small crystalline site assigned to `U` has the explicit
identity-thickening crystalline object as its underlying object. -/
#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineTrivialFunctor_obj :
    ∀ (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (U : X.smallZariskiSite),
    ((smallCrystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).obj U).obj.1 =
      trivialCrystallineObject I γ h_compatible X x₀ ((smallZariskiForget X).obj U))

end Crystalline
end Scheme
end AlgebraicGeometry
