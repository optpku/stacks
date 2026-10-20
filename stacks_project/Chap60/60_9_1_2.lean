/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.«60_9_1_2_Functor»
public import stacks_project.Chap60.«60_8_1_2»
public import stacks_project.Chap60.«60_9_1_1»

import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Crystalline

/-- 60.9.1.2: in Situation 60.7.5, the trivial crystalline functor
from `X.smallZariskiSite` to `smallCrystallineSite S I γ h_compatible X x₀`
sends an open object `U` to the identity thickening `(U, U, ∅)`. -/
@[stacks 07II]
noncomputable def smallCrystallineTrivialFunctor
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
    X.smallZariskiSite ⥤ smallCrystallineSite S I γ h_compatible X x₀ where
  obj := fun U ↦
    { obj := (crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).obj
        ((smallZariskiForget X).obj U)
      property := U.prop }
  map := fun {U V} f ↦
    ObjectProperty.homMk
      ((crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).map
        ((smallZariskiForget X).map f))
  map_id := sorry
  map_comp := sorry

/-- The object of the small crystalline site assigned to `U` has the explicit
identity-thickening crystalline object as its underlying object. -/
theorem smallCrystallineTrivialFunctor_obj
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
    (U : X.smallZariskiSite) :
    ((smallCrystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).obj U).obj.1 =
      trivialCrystallineObject I γ h_compatible X x₀ ((smallZariskiForget X).obj U) := sorry

end Crystalline
end Scheme
end AlgebraicGeometry
