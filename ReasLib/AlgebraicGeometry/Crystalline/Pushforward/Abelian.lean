/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.AlgebraicGeometry.Crystalline.ZariskiComparison

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

universe u v

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

/-- Direct image of abelian sheaves along `u_{X/S} : Cris(X/S) ⟶ X_Zariski`. -/
def smallCrystallinePushforward
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{v},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v} ⥤
      Sheaf X.smallZariskiTopology AddCommGrpCat.{v} :=
  (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).sheafPushforwardCocontinuous
    AddCommGrpCat.{v} (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    X.smallZariskiTopology

/-- Unfolding of `smallCrystallinePushforward` as cocontinuous sheaf pushforward. -/
theorem smallCrystallinePushforward_eq
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{v},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    smallCrystallinePushforward I γ h_compatible s x₀ h_p =
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).sheafPushforwardCocontinuous
        AddCommGrpCat.{v} (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        X.smallZariskiTopology := sorry

/-- The cocontinuous crystalline pushforward of abelian sheaves is additive. -/
instance smallCrystallinePushforward_additive
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{v},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    (smallCrystallinePushforward I γ h_compatible s x₀ h_p).Additive := sorry

/-- `Ru_{X/S,*}` as the K-injective total right derived functor of `u_{X/S,*}`. -/
def derivedSmallCrystallinePushforward
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{v},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{v}]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{v})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v})] :
    DerivedCategory
        (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}) ⥤
      DerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{v}) :=
  Functor.RightDerived.KInjective.functor
    (smallCrystallinePushforward I γ h_compatible s x₀ h_p)

/-- Unfolding of `derivedSmallCrystallinePushforward` as a K-injective right derived functor. -/
theorem derivedSmallCrystallinePushforward_eq
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{v},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{v}]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{v})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v})] :
    derivedSmallCrystallinePushforward I γ h_compatible s x₀ h_p =
      Functor.RightDerived.KInjective.functor
        (smallCrystallinePushforward I γ h_compatible s x₀ h_p) := sorry

/-- `Ru_{X/S,*}` applied to an abelian sheaf on `Cris(X/S)`, viewed as a complex concentrated in
degree zero. -/
def derivedSmallCrystallinePushforward_obj
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{v},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{v}]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{v})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v})]
    (G : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}) :
    DerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{v}) :=
  (Functor.RightDerived.KInjective.functor
      (smallCrystallinePushforward I γ h_compatible s x₀ h_p)).obj
    ((DerivedCategory.singleFunctor _ 0).obj G)

/-- Unfolding of `derivedSmallCrystallinePushforward_obj` through the degree-zero single functor. -/
theorem derivedSmallCrystallinePushforward_obj_eq
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{v},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{v}]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{v})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v})]
    (G : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}) :
    derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p G =
      (derivedSmallCrystallinePushforward I γ h_compatible s x₀ h_p).obj
        ((DerivedCategory.singleFunctor _ 0).obj G) := sorry

end AlgebraicGeometry.Scheme.Crystalline
