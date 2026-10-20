/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Definition_60_9_1
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Preserves
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/- The following instances record the continuity, cocontinuity, and finite
   nonempty-limit preservation asserted for the small crystalline forgetful
   functor in Remark 60.9.4. -/

/-- The small crystalline forgetful functor is continuous for the restricted
topology and the small Zariski topology. -/
instance forgetfulFunctor_isContinuous {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).IsContinuous
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      X.smallZariskiTopology := sorry

/-- The small crystalline forgetful functor is cocontinuous for the restricted
topology and the small Zariski topology. -/
instance forgetfulFunctor_isCocontinuous {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).IsCocontinuous
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      X.smallZariskiTopology := sorry

/-- The small crystalline forgetful functor preserves finite nonempty limits,
in particular products and fibre products. -/
instance forgetfulFunctor_preservesFiniteNonemptyLimits
    {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    PreservesFiniteNonemptyLimits
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p) := sorry

/-- The canonical morphism of topoi from the small crystalline topos to the
small Zariski topos, obtained from the cocontinuous forgetful functor. -/
noncomputable def smallCrystallineToposMorphism {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn X.smallZariskiTopology
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) :=
  (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).morphismOfTopoiInOfCocontinuous
    (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) X.smallZariskiTopology

/-- The inverse-image functor of `smallCrystallineToposMorphism` is the
sheafified pullback along the small crystalline forgetful functor. -/
theorem smallCrystallineToposMorphism_inverseImage
    {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    (smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).inverseImage =
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).sheafPullbackCocontinuous
        (Type (u + 1)) (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        X.smallZariskiTopology := sorry

/-- The direct-image functor of `smallCrystallineToposMorphism` is the
cocontinuous sheaf pushforward along the forgetful functor. -/
theorem smallCrystallineToposMorphism_pushforward
    {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    (smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).pushforward =
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).sheafPushforwardCocontinuous
        (Type (u + 1)) (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        X.smallZariskiTopology := sorry

end AlgebraicGeometry.Scheme.Crystalline

end
