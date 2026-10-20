/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ProperLowerShriek
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
variable (h_sq : CommSq g' f' f g)
variable [IsProper f] [IsProper f']
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [IsSeparated g'] [LocallyQuasiFinite g'] [LocallyOfFiniteType g']

variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]

variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]

variable [(etaleModulePushforward f Λ).Additive]
variable [(etaleModulePushforward f' Λ).Additive]
variable [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
variable [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

/- Lemma 63.8.1: the canonical comparison for a commutative square with proper
vertical maps and separated locally quasi-finite horizontal maps. -/
@[stacks 0F7B] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ :
  etaleDerivedPushforward f' ⋙ lowerShriekModuleDerived g Λ ⟶
    lowerShriekModuleDerived g' Λ ⋙ etaleDerivedPushforward f)

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekPushforward_isIso_of_isGE_isTorsion f f' g g' h_sq Λ :
  ∀ (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))), etaleDerivedIsTorsion K →
    ∀ (n : ℤ), [DerivedCategory.IsGE K n] →
      IsIso ((etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K))

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekPushforward_isIso_of_isTorsion f f' g g' h_sq Λ :
  AddMonoid.IsTorsion Λ → ∀ (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))),
    IsIso ((etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K))

end AlgebraicGeometry.Scheme.Etale

end
