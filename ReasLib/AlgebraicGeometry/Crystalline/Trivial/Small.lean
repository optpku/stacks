/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Trivial
public import ReasLib.AlgebraicGeometry.Crystalline.Site

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- The trivial crystalline functor from the small Zariski category to the small crystalline
category sends each open source to its identity thickening with zero ideal. -/
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
    X.smallZariskiSite ⥤ smallCrystallineSite S I γ h_compatible X x₀ :=
  ObjectProperty.lift (smallCrystallineProperty S I γ h_compatible X x₀)
    (smallZariskiForget X ⋙ crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p)
    (fun U ↦ U.prop)

/-- The underlying crystalline object assigned to an open source by the small trivial functor
is its identity thickening with zero ideal. -/
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

end AlgebraicGeometry.Scheme.Crystalline
