/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Thickening
public import Mathlib.Topology.Sheaves.Functors

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Crystalline

universe u v

noncomputable section

/-- Inverse image of a Type-valued Zariski sheaf along the underlying continuous map of a
thickening morphism. -/
def crystallineInverseImage (C : Type v) [Category C]
    (thickening : C ⥤ Scheme.{u}) {A B : C} (f : A ⟶ B) :
    TopCat.Sheaf (Type u) (thickening.obj B).toTopCat ⥤
      TopCat.Sheaf (Type u) (thickening.obj A).toTopCat :=
  TopCat.Sheaf.pullback (Type u) (thickening.map f).base

/-- A family of sheaves on thickening schemes with chosen comparison maps, without
coherence or invertibility conditions. -/
structure CrystallineSheaf (C : Type v) [Category C]
    (thickening : C ⥤ Scheme.{u}) where
  /-- The sheaf assigned to each object of the crystalline category. -/
  obj : ∀ A : C, TopCat.Sheaf (Type u) (thickening.obj A).toTopCat
  /-- The chosen comparison map from the pullback along a crystalline morphism. -/
  comparison : ∀ {A B : C} (f : A ⟶ B),
    (crystallineInverseImage C thickening f).obj (obj B) ⟶ obj A

/-- Construct a family of sheaves from its objectwise sheaves and chosen comparison maps. -/
def CrystallineSheaf.of {C : Type v} [Category C]
    (thickening : C ⥤ Scheme.{u})
    (obj : ∀ A : C, TopCat.Sheaf (Type u) (thickening.obj A).toTopCat)
    (comparison : ∀ {A B : C} (f : A ⟶ B),
      (crystallineInverseImage C thickening f).obj (obj B) ⟶ obj A) :
    CrystallineSheaf C thickening :=
  { obj, comparison }

/-- The family constructor has the supplied objectwise sheaves and comparison maps. -/
theorem CrystallineSheaf.of_spec {C : Type v} [Category C]
    (thickening : C ⥤ Scheme.{u})
    (obj : ∀ A : C, TopCat.Sheaf (Type u) (thickening.obj A).toTopCat)
    (comparison : ∀ {A B : C} (f : A ⟶ B),
      (crystallineInverseImage C thickening f).obj (obj B) ⟶ obj A) :
    (CrystallineSheaf.of thickening obj comparison).obj = obj ∧
      ∀ {A B : C} (f : A ⟶ B),
        (CrystallineSheaf.of thickening obj comparison).comparison f = comparison f := sorry

namespace CrystallineSheaf

/-- Families of Zariski sheaves with chosen comparison maps on the big crystalline category. -/
abbrev Big
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :=
  CrystallineSheaf (RelativeCRIS S I γ h_compatible X x₀)
    (AlgebraicGeometry.Scheme.Crystalline.thickeningFunctor S I γ h_compatible X x₀)

/-- Families of Zariski sheaves with chosen comparison maps on the small crystalline category. -/
abbrev Small
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :=
  CrystallineSheaf (smallCrystallineSite S I γ h_compatible X x₀)
    (AlgebraicGeometry.Scheme.Crystalline.smallThickeningFunctor S I γ h_compatible X x₀)

end CrystallineSheaf

namespace AlgebraicGeometry.Scheme.Crystalline.Sheaf

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible : ∀ (V : S.affineOpens) (g : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
      (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Restriction of a crystalline sheaf to the opens of a thickening. -/
def restrictPresheaf
    (F : CategoryTheory.Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) (Type u))
    (A : RelativeCRIS S I γ h_compatible X x₀) :
    TopCat.Presheaf (Type u) A.1.thickening.toTopCat :=
  (relativeOpensFunctor A).op ⋙ F.obj

/-- Restriction of a crystalline sheaf to a thickening satisfies the Zariski sheaf condition. -/
theorem restrictPresheaf_isSheaf
    (F : CategoryTheory.Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) (Type u))
    (A : RelativeCRIS S I γ h_compatible X x₀) :
    TopCat.Presheaf.IsSheaf (restrictPresheaf F A) := sorry

/-- The Zariski sheaf obtained by restricting a crystalline sheaf to a thickening. -/
def restrictObj
    (F : CategoryTheory.Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) (Type u))
    (A : RelativeCRIS S I γ h_compatible X x₀) :
    TopCat.Sheaf (Type u) A.1.thickening.toTopCat :=
  ⟨restrictPresheaf F A, restrictPresheaf_isSheaf F A⟩

/-- Maps on open crystalline restrictions give a morphism into the direct image sheaf. -/
def comparisonPushforward
    (F : CategoryTheory.Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) (Type u))
    {A B : RelativeCRIS S I γ h_compatible X x₀} (f : A ⟶ B) :
    restrictObj F B ⟶
      (TopCat.Sheaf.pushforward (Type u) f.thickening.base).obj (restrictObj F A) :=
  ObjectProperty.homMk
    { app U := F.obj.map (Quiver.Hom.op (CrystallineObject.Hom.restrictOpen f U.unop :
          relativeRestrictOpen A (f.thickening ⁻¹ᵁ U.unop) ⟶ relativeRestrictOpen B U.unop))
      naturality := sorry }

/-- A crystalline morphism induces a comparison from the inverse image of the target restriction
to the source restriction. -/
def comparison
    (F : CategoryTheory.Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) (Type u))
    {A B : RelativeCRIS S I γ h_compatible X x₀} (f : A ⟶ B) :
    (TopCat.Sheaf.pullback (Type u) f.thickening.base).obj (restrictObj F B) ⟶
      restrictObj F A :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.thickening.base).homEquiv _ _).symm
    (comparisonPushforward F f)

/-- The adjoint of a restriction comparison acts by the original sheaf map on each open. -/
theorem comparison_spec
    (F : CategoryTheory.Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) (Type u))
    {A B : RelativeCRIS S I γ h_compatible X x₀} (f : A ⟶ B)
    (U : B.1.thickening.Opens) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.thickening.base).homEquiv _ _)
      (comparison F f)).hom.app (op U) =
        F.obj.map (Quiver.Hom.op (CrystallineObject.Hom.restrictOpen f U :
          relativeRestrictOpen A (f.thickening ⁻¹ᵁ U) ⟶ relativeRestrictOpen B U)) := sorry

/-- Restriction of a small crystalline sheaf to the opens of a thickening. -/
def smallRestrictPresheaf
    (F : CategoryTheory.Sheaf
      (smallCrystallineZariskiPrecoverage S I γ h_compatible X x₀).toGrothendieck (Type u))
    (A : smallCrystallineSite S I γ h_compatible X x₀) :
    TopCat.Presheaf (Type u) A.obj.1.thickening.toTopCat :=
  (smallOpensFunctor A).op ⋙ F.obj

/-- Restriction of a small crystalline sheaf satisfies the Zariski sheaf condition. -/
theorem smallRestrictPresheaf_isSheaf
    (F : CategoryTheory.Sheaf
      (smallCrystallineZariskiPrecoverage S I γ h_compatible X x₀).toGrothendieck (Type u))
    (A : smallCrystallineSite S I γ h_compatible X x₀) :
    TopCat.Presheaf.IsSheaf (smallRestrictPresheaf F A) := sorry

/-- The Zariski sheaf obtained by restricting a small crystalline sheaf to a thickening. -/
def smallRestrictObj
    (F : CategoryTheory.Sheaf
      (smallCrystallineZariskiPrecoverage S I γ h_compatible X x₀).toGrothendieck (Type u))
    (A : smallCrystallineSite S I γ h_compatible X x₀) :
    TopCat.Sheaf (Type u) A.obj.1.thickening.toTopCat :=
  ⟨smallRestrictPresheaf F A, smallRestrictPresheaf_isSheaf F A⟩

/-- Maps on small crystalline open restrictions give a morphism into the direct image sheaf. -/
def smallComparisonPushforward
    (F : CategoryTheory.Sheaf
      (smallCrystallineZariskiPrecoverage S I γ h_compatible X x₀).toGrothendieck (Type u))
    {A B : smallCrystallineSite S I γ h_compatible X x₀} (f : A ⟶ B) :
    smallRestrictObj F B ⟶
      (TopCat.Sheaf.pushforward (Type u) f.hom.thickening.base).obj (smallRestrictObj F A) :=
  ObjectProperty.homMk
    { app U := F.obj.map (ObjectProperty.homMk
          (CrystallineObject.Hom.restrictOpen f.hom U.unop)).op
      naturality := sorry }

/-- A small crystalline morphism induces the inverse-image comparison of restricted sheaves. -/
def smallComparison
    (F : CategoryTheory.Sheaf
      (smallCrystallineZariskiPrecoverage S I γ h_compatible X x₀).toGrothendieck (Type u))
    {A B : smallCrystallineSite S I γ h_compatible X x₀} (f : A ⟶ B) :
    (TopCat.Sheaf.pullback (Type u) f.hom.thickening.base).obj (smallRestrictObj F B) ⟶
      smallRestrictObj F A :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.hom.thickening.base).homEquiv _ _).symm
    (smallComparisonPushforward F f)

/-- The adjoint of a small restriction comparison acts by the original sheaf map on each open. -/
theorem smallComparison_spec
    (F : CategoryTheory.Sheaf
      (smallCrystallineZariskiPrecoverage S I γ h_compatible X x₀).toGrothendieck (Type u))
    {A B : smallCrystallineSite S I γ h_compatible X x₀} (f : A ⟶ B)
    (U : B.obj.1.thickening.Opens) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.hom.thickening.base).homEquiv _ _)
      (smallComparison F f)).hom.app (op U) =
        F.obj.map (ObjectProperty.homMk (CrystallineObject.Hom.restrictOpen f.hom U)).op := sorry

end AlgebraicGeometry.Scheme.Crystalline.Sheaf
