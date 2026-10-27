/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Zariski
public import ReasLib.AlgebraicGeometry.Crystalline.ZariskiComparison
public import ReasLib.AlgebraicGeometry.Crystalline.Inclusion
public import ReasLib.CategoryTheory.Sites.BeckChevalley
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- Forgetting the crystalline thickening commutes with small-to-big inclusion:
both paths retain the same source scheme over the base source. -/
@[implicit_reducible]
def smallBigZariskiSquare :
    CatCommSq (smallCrystallineInclusion S I γ h_compatible X x₀) (forgetfulFunctor p S I γ h_compatible s X x₀ h_p) (crystallineForgetful S I γ h_compatible s X x₀ h_p) (Zariski.SmallToBig.relocalizationFunctor (𝟙 X)) where
  iso :=
    (Functor.rightUnitor ((smallCrystallineInclusion S I γ h_compatible X x₀) ⋙ (crystallineForgetful S I γ h_compatible s X x₀ h_p))).symm ≪≫
      Functor.isoWhiskerLeft ((smallCrystallineInclusion S I γ h_compatible X x₀) ⋙ (crystallineForgetful S I γ h_compatible s X x₀ h_p)) (Over.mapId X).symm

variable [h_quasiCoherent : I.toModule.IsQuasicoherent]
variable [HasWeakSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) (Type w)]
variable [HasWeakSheafify (crystallineZariskiTopology S I γ h_compatible X x₀) (Type w)]
variable [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type w,
  (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
variable [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type w,
  (crystallineForgetful S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]

/-- The Beck–Chevalley map compares big crystalline direct image restricted to
small Zariski objects with direct image after restriction to small crystalline objects. -/
def smallBigZariskiComparison :
    (crystallineForgetful S I γ h_compatible s X x₀ h_p).sheafPushforwardCocontinuous (Type w)
      (crystallineZariskiTopology S I γ h_compatible X x₀) X.bigZariskiTopology ⋙
    (Zariski.SmallToBig.relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous (Type w)
      X.smallZariskiTopology X.bigZariskiTopology ⟶
    (smallCrystallineInclusion S I γ h_compatible X x₀).sheafPushforwardContinuous (Type w) (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) (crystallineZariskiTopology S I γ h_compatible X x₀) ⋙
    (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).sheafPushforwardCocontinuous (Type w)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) X.smallZariskiTopology :=
  CatCommSq.BeckChevalley.comparison (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) (crystallineZariskiTopology S I γ h_compatible X x₀)
    X.smallZariskiTopology X.bigZariskiTopology
    (smallBigZariskiSquare I γ h_compatible s x₀ h_p)

/-- Restriction from big to small crystalline objects is compatible with crystalline
Zariski direct image: the source-forgetting Beck–Chevalley map is invertible. -/
instance smallBigZariskiComparison_isIso :
    IsIso (smallBigZariskiComparison.{u, w} I γ h_compatible s x₀ h_p) := sorry

/-- The canonical isomorphism between the big and small crystalline presentations
of crystalline Zariski direct image. -/
def smallBigZariskiComparisonIso :
    (crystallineForgetful S I γ h_compatible s X x₀ h_p).sheafPushforwardCocontinuous (Type w)
      (crystallineZariskiTopology S I γ h_compatible X x₀) X.bigZariskiTopology ⋙
    (Zariski.SmallToBig.relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous (Type w)
      X.smallZariskiTopology X.bigZariskiTopology ≅
    (smallCrystallineInclusion S I γ h_compatible X x₀).sheafPushforwardContinuous (Type w) (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) (crystallineZariskiTopology S I γ h_compatible X x₀) ⋙
    (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).sheafPushforwardCocontinuous (Type w)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) X.smallZariskiTopology :=
  asIso (smallBigZariskiComparison I γ h_compatible s x₀ h_p)

end AlgebraicGeometry.Scheme.Crystalline
