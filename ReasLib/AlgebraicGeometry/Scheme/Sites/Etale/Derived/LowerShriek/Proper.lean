/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain

/-!
# Derived lower shriek and proper pushforward in a commutative triangle
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}}
variable (f : X ⟶ Y) (h : Y ⟶ Z) {g : X ⟶ Z}
variable (w : f ≫ h = g)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [IsProper h]
variable [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]

-- Module visibility: allow this private construction in the public comparison.
set_option backward.privateInPublic true in
/-- The cochain composite maps to the iterated derived functor via the unit
for proper pushforward after exact compact-support direct image. -/
private def etaleDerivedLowerShriekProper_unit
    [((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive]
    [(lowerShriekModule f Λ ⋙ ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.toDerived
        (lowerShriekModule f Λ ⋙ ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
            DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (lowerShriekModuleDerived f Λ ⋙ etaleDerivedPushforward h) :=
  RightDerived.Cochain.ExactFirst.unit
    (ExactFunctor.of (lowerShriekModule f Λ))
    ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)

-- Module visibility: retain the concrete construction as a private implementation detail.
set_option backward.privateInPublic true in
/-- The canonical derived comparison from compact-support direct image along
`g` to proper derived pushforward after compact-support direct image along `f`,
for a commutative triangle `f ≫ h = g`. -/
def etaleDerivedLowerShriekProper
    [((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive]
    [(lowerShriekModule f Λ ⋙ ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    lowerShriekModuleDerived g Λ ⟶
      lowerShriekModuleDerived f Λ ⋙ etaleDerivedPushforward h :=
  let e := Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex
      (lowerShriekModule_compProperIso f h w Λ) (ComplexShape.up ℤ))
    (DerivedCategory.Q :
      CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))
  (lowerShriekModule g Λ).mapDerivedCategory.rightDerivedDesc
    (lowerShriekModule g Λ).mapDerivedCategoryFactors.inv
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (lowerShriekModuleDerived f Λ ⋙ etaleDerivedPushforward h)
    (e.hom ≫ etaleDerivedLowerShriekProper_unit f h Λ)

/-- The proper-triangle derived comparison is invertible on bounded-below
objects with torsion cohomology sheaves. -/
theorem etaleDerivedLowerShriekProper_isIso_of_isGE_isTorsion
    [((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive]
    [(lowerShriekModule f Λ ⋙ ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n] :
    IsIso ((etaleDerivedLowerShriekProper f h w Λ).app K) := sorry

/-- The proper-triangle derived comparison is invertible on every object
when the coefficient ring is additively torsion. -/
theorem etaleDerivedLowerShriekProper_isIso_of_isTorsion
    [((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive]
    [(lowerShriekModule f Λ ⋙ ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (hΛ : AddMonoid.IsTorsion Λ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIso ((etaleDerivedLowerShriekProper f h w Λ).app K) := sorry

/-- The proper-triangle derived comparison is invertible on admissible objects. -/
instance etaleDerivedLowerShriekProper_app_isIso
    [((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive]
    [(lowerShriekModule f Λ ⋙ ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    [hK : Fact (Derived.compactSupportAdmissible X Λ K)] :
    IsIso ((etaleDerivedLowerShriekProper f h w Λ).app K) := by
  rcases hK.out with ⟨h_tors, n, hn⟩ | hΛ
  · exact etaleDerivedLowerShriekProper_isIso_of_isGE_isTorsion f h w Λ K h_tors n
  · exact etaleDerivedLowerShriekProper_isIso_of_isTorsion f h w Λ hΛ K

end AlgebraicGeometry.Scheme.Etale

end
