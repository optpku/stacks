/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap60.Lemma_60_9_2_Inclusion
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- The inclusion induces `i : (X/S)_cris ⟶ (X/S)_CRIS`. -/
noncomputable def smallToBigCrystallineToposMorphism
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))] :
    MorphismOfTopoiIn
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) :=
  (smallCrystallineInclusion S I γ h_compatible X x₀).morphismOfTopoiInOfCocontinuous
    (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    (crystallineZariskiTopology S I γ h_compatible X x₀)

/-- Inverse image of `i` is the sheafified cocontinuous pullback along the inclusion. -/
theorem smallToBigCrystallineToposMorphism_inverseImage
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))] :
    (smallToBigCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p).inverseImage =
      (smallCrystallineInclusion S I γ h_compatible X x₀).sheafPullbackCocontinuous
        (Type (u + 1))
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        (crystallineZariskiTopology S I γ h_compatible X x₀) := sorry

/-- The sheaf pullback along the inclusion preserves finite limits, so `i_!` is exact. -/
instance smallCrystallineInclusion_sheafPullback_preservesFiniteLimits
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((smallCrystallineInclusion S I γ h_compatible X x₀).sheafPullback (Type (u + 1))
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        (crystallineZariskiTopology S I γ h_compatible X x₀)) := sorry

/-- There is `π : (X/S)_CRIS ⟶ (X/S)_cris` with `π⁻¹ = i_!`. -/
noncomputable def bigToSmallCrystallineToposMorphism
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P] :
    MorphismOfTopoiIn
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀) :=
  (smallCrystallineInclusion S I γ h_compatible X x₀).morphismOfTopoiInOfContinuous
    (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    (crystallineZariskiTopology S I γ h_compatible X x₀)

/-- Direct image of `π` is continuous sheaf pushforward of the inclusion. -/
theorem bigToSmallCrystallineToposMorphism_pushforward
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P] :
    (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p).pushforward =
      (smallCrystallineInclusion S I γ h_compatible X x₀).sheafPushforwardContinuous
        (Type (u + 1))
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        (crystallineZariskiTopology S I γ h_compatible X x₀) := sorry

/-- Inverse image of `π` is sheaf pullback of the inclusion. -/
theorem bigToSmallCrystallineToposMorphism_inverseImage
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P] :
    (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p).inverseImage =
      (smallCrystallineInclusion S I γ h_compatible X x₀).sheafPullback (Type (u + 1))
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        (crystallineZariskiTopology S I γ h_compatible X x₀) := sorry

/-- The composite `π ∘ i` is the identity on `(X/S)_cris`. -/
theorem bigToSmallCrystallineToposMorphism_comp_smallToBig
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P] :
    MorphismOfTopoiIn.comp
        (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p)
        (smallToBigCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p) =
      MorphismOfTopoiIn.id
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) := sorry

/-- `π_* = i⁻¹`. -/
theorem bigToSmallCrystallineToposMorphism_pushforward_eq_inverseImage
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P] :
    (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p).pushforward =
      (smallToBigCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p).inverseImage := sorry

end AlgebraicGeometry.Scheme.Crystalline
