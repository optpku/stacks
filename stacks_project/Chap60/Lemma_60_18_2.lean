/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import stacks_project.Chap60.Definition_60_11_1_ModuleProperties
public import stacks_project.Chap60.Definition_60_9_1
public import stacks_project.Chap60.Lemma_60_18_2_Site
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf

@[expose] public section

noncomputable section

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

/-- Global sections of a module sheaf, viewed as an abelian group. -/
def abelianGlobalSections {Y : Scheme.{u}} (M : Y.Modules) : AddCommGrpCat.{u} :=
  (Scheme.Modules.presheaf M).obj (op ⊤)

/-- Unfolding of abelian global sections as top-open values of the underlying presheaf. -/
theorem abelianGlobalSections_eq {Y : Scheme.{u}} (M : Y.Modules) :
    abelianGlobalSections M = (Scheme.Modules.presheaf M).obj (op ⊤) :=
  sorry

/-- Global sections along a thickening morphism, after applying a module comparison. -/
def abelianGlobalSections_map {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {MY : Y.Modules} {MZ : Z.Modules}
    (φ : (Scheme.Modules.pullback f).obj MZ ⟶ MY) :
    abelianGlobalSections MZ ⟶ abelianGlobalSections MY :=
  Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app MZ) ⊤ ≫
    eqToHom
      (by
        have hU : f ⁻¹ᵁ (⊤ : Z.Opens) = ⊤ := rfl
        change
          (Scheme.Modules.presheaf
              ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj MZ))).obj
            (op ⊤) =
          (Scheme.Modules.presheaf ((Scheme.Modules.pullback f).obj MZ)).obj (op ⊤)
        simp [Scheme.Modules.pushforward_obj_obj, hU]) ≫
    Modules.Hom.app φ ⊤

/-- Underlying thickening morphism of a morphism of small crystalline objects. -/
def smallCrystallineHom_thickening
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) :=
  f.hom.thickening

/-- The thickening morphism of a small crystalline morphism is the hom-component thickening. -/
theorem smallCrystallineHom_thickening_eq
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) :
    smallCrystallineHom_thickening S I γ h_compatible X x₀ f = f.hom.thickening :=
  sorry

/-- The abelian presheaf of global sections of a crystalline module sheaf on `Cris(X/S)`. -/
def toAbelianPresheaf (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := abelianGlobalSections (F.obj T.unop)
  map {T U} f :=
    abelianGlobalSections_map
      (smallCrystallineHom_thickening S I γ h_compatible X x₀ f.unop)
      (F.comparison f.unop)
  map_id := sorry
  map_comp := sorry

/-- Underlying abelian sheaf of a crystalline module sheaf on the small crystalline site. -/
def toAbelianSheaf
    [HasWeakSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}]
    (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} :=
  (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}).obj
    (toAbelianPresheaf S I γ h_compatible X x₀ F)

/-- Sheafification of the global-section presheaf recovers `toAbelianSheaf`. -/
theorem toAbelianSheaf_obj
    [HasWeakSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}]
    (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    toAbelianSheaf p S I γ h_compatible s X x₀ h_p F =
      (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          AddCommGrpCat.{u}).obj
        (toAbelianPresheaf S I γ h_compatible X x₀ F) :=
  sorry

/-- Restriction of an abelian sheaf on `Cris(X/S)` to the chaotic whole-source subcategory. -/
def restrictToChaotic
    (F : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}) :
    Sheaf (chaoticTopology S I γ h_compatible X x₀) AddCommGrpCat.{u} where
  obj := (chaoticInclusion S I γ h_compatible X x₀).op ⋙ F.obj
  property := sorry

/-- Restriction to the chaotic site is composition with the opposite inclusion. -/
theorem restrictToChaotic_obj
    (F : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}) :
    (restrictToChaotic p S I γ h_compatible s X x₀ h_p F).obj =
      (chaoticInclusion S I γ h_compatible X x₀).op ⋙ F.obj :=
  sorry

/-- Lemma 60.18.2: in Situation 60.7.5, if `X` and `S` are affine, then for every locally
quasi-coherent `𝒪_{X/S}`-module `F` the derived global sections on the chaotic full
subcategory of whole-source objects `(X, T, δ)` recover the derived global sections on
`Cris(X/S)`. -/
@[stacks 07JK]
theorem locallyQuasiCoherent_derivedGlobalSections_iso_chaotic
    [IsAffine X] [IsAffine S]
    [HasSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}]
    [HasSheafify (chaoticTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasTerminal (smallCrystallineSite S I γ h_compatible X x₀)]
    [HasTerminal (chaoticSite S I γ h_compatible X x₀)]
    [HasDerivedCategory AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (chaoticTopology S I γ h_compatible X x₀) AddCommGrpCat.{u})]
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F] :
    IsIsomorphic
      ((siteAbelianSectionsDerived (chaoticTopology S I γ h_compatible X x₀)
          (⊤_ (chaoticSite S I γ h_compatible X x₀))).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (chaoticTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}) 0).obj
          (restrictToChaotic p S I γ h_compatible s X x₀ h_p
            (toAbelianSheaf p S I γ h_compatible s X x₀ h_p F))))
      ((siteAbelianSectionsDerived
          (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          (⊤_ (smallCrystallineSite S I γ h_compatible X x₀))).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
              AddCommGrpCat.{u}) 0).obj
          (toAbelianSheaf p S I γ h_compatible s X x₀ h_p F))) :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline
