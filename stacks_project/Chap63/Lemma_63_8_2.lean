module

public import stacks_project.Chap63.Lemma_63_8_2_Comparison

/-!
# Vertical composition of derived lower shriek / proper pushforward comparisons

Lemma 63.8.2: for a vertically stacked pair of commutative squares of schemes,
with proper vertical maps and separated locally quasi-finite horizontal maps,
the Lemma 63.8.1 comparisons of the two squares paste to the comparison of the
outer rectangle after identifying `R(g ∘ f)_*` with `Rg_* ∘ Rf_*`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X' X Y' Y Z' Z : Scheme.{u}}
variable (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y ⟶ Z) (g' : Y' ⟶ Z')
variable (k : X' ⟶ X) (l : Y' ⟶ Y) (m : Z' ⟶ Z)
variable (h_top : CommSq k f' f l) (h_bot : CommSq l g' g m)
variable [IsProper f] [IsProper f'] [IsProper g] [IsProper g']
variable [IsSeparated k] [LocallyQuasiFinite k] [LocallyOfFiniteType k]
variable [IsSeparated l] [LocallyQuasiFinite l] [LocallyOfFiniteType l]
variable [IsSeparated m] [LocallyQuasiFinite m] [LocallyOfFiniteType m]
variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z'.Etale,
  HasWeakSheafify (Z'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Lemma 63.8.2: Consider a commutative diagram of schemes with vertical maps
`f`, `f'`, `g`, `g'` proper and horizontal maps `k`, `l`, `m` separated and
locally quasi-finite. After identifying `R(g ∘ f)_*` with `Rg_* ∘ Rf_*` and
`R(g' ∘ f')_*` with `Rg'_* ∘ Rf'_*` via `etaleDerivedPushforwardComp`, the
Lemma 63.8.1 comparison of the outer rectangle equals the composite of the
two square comparisons
`m_! ∘ Rg'_* ∘ Rf'_* ⟶ Rg_* ∘ l_! ∘ Rf'_* ⟶ Rg_* ∘ Rf_* ∘ k_!`. -/
@[stacks 0F7C]
theorem etaleDerivedLowerShriekPushforward_vcomp
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward (f ≫ g) Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward (f ≫ g) Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f' ≫ g') Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (f' ≫ g') Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward (f ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedLowerShriekPushforward_vcomp_inner f f' g g' k l m h_top h_bot Λ =
      etaleDerivedLowerShriekPushforward_vcomp_outer f f' g g' k l m
        h_top h_bot Λ :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
