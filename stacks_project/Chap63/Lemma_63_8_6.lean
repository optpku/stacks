/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Proper
import StacksCheckRecall

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

/- Lemma 63.8.6: For a commutative triangle with locally quasi-finite `f`
and `g` and proper `h`, there is a canonical map `g_! K ⟶ Rh_*(f_! K)`.
It is invertible for bounded-below torsion cohomology or torsion coefficients. -/
@[stacks 0F7G] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekProper f h w Λ :
  [((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive] →
  [(lowerShriekModule f Λ ⋙ ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)).Additive] →
  [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] →
  lowerShriekModuleDerived g Λ ⟶
    lowerShriekModuleDerived f Λ ⋙ etaleDerivedPushforward h)

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekProper_isIso_of_isGE_isTorsion f h w Λ :
  [((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive] →
  [(lowerShriekModule f Λ ⋙ ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)).Additive] →
  [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] →
  (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) →
  etaleDerivedIsTorsion K → (n : ℤ) → [DerivedCategory.IsGE K n] →
  IsIso ((etaleDerivedLowerShriekProper f h w Λ).app K))

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekProper_isIso_of_isTorsion f h w Λ :
  [((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).Additive] →
  [(lowerShriekModule f Λ ⋙ ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)).Additive] →
  [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] →
  AddMonoid.IsTorsion Λ →
  (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) →
  IsIso ((etaleDerivedLowerShriekProper f h w Λ).app K))

end AlgebraicGeometry.Scheme.Etale

end
