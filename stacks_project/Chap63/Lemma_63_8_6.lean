/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_8_6_Comparison
import StacksCheckRecall

/-!
# Derived comparison of locally quasi-finite lower shriek with proper pushforward

Lemma 63.8.6: for a commutative triangle of schemes with locally quasi-finite
`f`, `g` and proper `h`, there is a canonical functorial map
`g_! K ⟶ Rh_*(f_! K)` in `D(Z_étale, Λ)`, which is an isomorphism if `K` is
bounded below with torsion cohomology sheaves, or if `Λ` is a torsion ring.
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

variable {X Y Z : Scheme.{u}}
variable (f : X ⟶ Y) (h : Y ⟶ Z) {g : X ⟶ Z}
variable (w : f ≫ h = g)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [IsProper h]
variable [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable (Λ : Type u) [CommRing Λ]
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

/- Lemma 63.8.6 (1): Consider a commutative diagram of schemes
`X ⟶ Y`, `Y ⟶ Z`, `X ⟶ Z` with `f` and `g` locally quasi-finite and `h`
proper. Let `Λ` be a ring. Functorially in `K ∈ D(X_étale, Λ)` there is a
canonical map `g_! K ⟶ Rh_*(f_! K)` in `D(Z_étale, Λ)`. -/
@[stacks 0F7G]
#check etaleDerivedLowerShriekProper

/-- Lemma 63.8.6 (2): the comparison `g_! K ⟶ Rh_*(f_! K)` is an isomorphism
if `K` is bounded below and has torsion cohomology sheaves. -/
@[stacks 0F7G]
theorem etaleDerivedLowerShriekProper_isIso_of_isGE_isTorsion
    [(etaleModulePushforward h Λ).Additive]
    [(lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X Λ) (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    [DerivedCategory.IsGE K n] :
    IsIso ((etaleDerivedLowerShriekProper f h w Λ).app K) :=
  sorry

/-- Lemma 63.8.6 (3): the comparison `g_! K ⟶ Rh_*(f_! K)` is an isomorphism
if `Λ` is a torsion ring. -/
@[stacks 0F7G]
theorem etaleDerivedLowerShriekProper_isIso_of_isTorsion
    [(etaleModulePushforward h Λ).Additive]
    [(lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived X Λ) :
    IsIso ((etaleDerivedLowerShriekProper f h w Λ).app K) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
