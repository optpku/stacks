/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import stacks_project.Chap63.Lemma_63_8_1_Comparison
import StacksCheckRecall

/-!
# Derived comparison of lower shriek and proper pushforward

Lemma 63.8.1: for a commutative square of schemes with proper vertical maps
and separated locally quasi-finite horizontal maps, there is a canonical
functorial map `g_! Rf'_* K ⟶ Rf_* (g'_! K)` in `D(Y_étale, Λ)`, which is an
isomorphism if `K` is bounded below with torsion cohomology sheaves, or if
`Λ` is a torsion ring.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
variable (h_sq : CommSq g' f' f g)
variable [IsProper f] [IsProper f']
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [IsSeparated g'] [LocallyQuasiFinite g'] [LocallyOfFiniteType g']
variable (Λ : Type u) [CommRing Λ]
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

/- Lemma 63.8.1 (1): Consider a commutative diagram of schemes
`X' ⟶ X`, `Y' ⟶ Y` with `f` and `f'` proper and `g` and `g'` separated and
locally quasi-finite. Let `Λ` be a ring. Functorially in
`K ∈ D(X'_étale, Λ)` there is a canonical map
`g_! Rf'_* K ⟶ Rf_* (g'_! K)` in `D(Y_étale, Λ)`. -/
@[stacks 0F7B]
#check etaleDerivedLowerShriekPushforward

/-- Lemma 63.8.1 (2): the comparison `g_! Rf'_* K ⟶ Rf_* (g'_! K)` is an
isomorphism if `K` is bounded below and has torsion cohomology sheaves. -/
@[stacks 0F7B]
theorem etaleDerivedLowerShriekPushforward_isIso_of_isGE_isTorsion
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X' Λ) (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    [DerivedCategory.IsGE K n] :
    IsIso ((etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K) :=
  sorry

/-- Lemma 63.8.1 (3): the comparison `g_! Rf'_* K ⟶ Rf_* (g'_! K)` is an
isomorphism if `Λ` is a torsion ring. -/
@[stacks 0F7B]
theorem etaleDerivedLowerShriekPushforward_isIso_of_isTorsion
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived X' Λ) :
    IsIso ((etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
