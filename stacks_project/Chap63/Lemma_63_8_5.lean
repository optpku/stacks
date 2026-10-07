module

public import stacks_project.Chap63.Lemma_63_8_5_Comparison
public import stacks_project.Chap63.Lemma_63_8_5_Pullback

/-!
# Base change of the derived lower shriek / proper pushforward comparison

Lemma 63.8.5: after base change along `b : Y₁ ⟶ Y`, the Lemma 63.8.1
vertical comparisons commute with the `Rf_*` base-change maps of Étale
Cohomology, Section 59.86 and the compact-support base-change maps of
Lemma 63.3.12.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' X₁ Y₁ X'₁ Y'₁ : Scheme.{u}}
variable (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
variable (h_sq : CommSq g' f' f g)
variable (b : Y₁ ⟶ Y) (b' : Y'₁ ⟶ Y') (a : X₁ ⟶ X) (a' : X'₁ ⟶ X')
variable (f₁ : X₁ ⟶ Y₁) (f'₁ : X'₁ ⟶ Y'₁) (g₁ : Y'₁ ⟶ Y₁) (g'₁ : X'₁ ⟶ X₁)
variable (h_sq₁ : CommSq g'₁ f'₁ f₁ g₁)
variable (h_Y' : IsPullback b' g₁ g b) (h_X : IsPullback a f₁ f b)
variable (h_X' : IsPullback a' f'₁ f' b') (h_back : IsPullback a' g'₁ g' a)
variable [IsProper f] [IsProper f'] [IsProper f₁] [IsProper f'₁]
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [IsSeparated g'] [LocallyQuasiFinite g'] [LocallyOfFiniteType g']
variable [IsSeparated g₁] [LocallyQuasiFinite g₁] [LocallyOfFiniteType g₁]
variable [IsSeparated g'₁] [LocallyQuasiFinite g'₁] [LocallyOfFiniteType g'₁]
variable (Λ : Type u) [CommRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X₁.Etale,
  HasWeakSheafify (X₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y₁.Etale,
  HasWeakSheafify (Y₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'₁.Etale,
  HasWeakSheafify (X'₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'₁.Etale,
  HasWeakSheafify (Y'₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback b).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback b').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback a).op.HasLeftKanExtension P]
variable [∀ P : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback a').op.HasLeftKanExtension P]
variable [∀ P : Y₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f₁).op.HasLeftKanExtension P]
variable [∀ P : Y'₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f'₁).op.HasLeftKanExtension P]
variable [∀ P : Y₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g₁).op.HasLeftKanExtension P]
variable [∀ P : X₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g'₁).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g₁ ≫ b)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (b' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f₁ ≫ b)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a ≫ f)).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f'₁ ≫ b')).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a' ≫ f')).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g'₁ ≫ a)).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a' ≫ g')).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback b).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback b').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback a).op.HasLeftKanExtension P]
variable [∀ P : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback a').op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback b).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback b').op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback a).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback a').op]

/-- Lemma 63.8.5: Let `b : Y₁ ⟶ Y` be a morphism of schemes. Consider a
commutative diagram of schemes with vertical maps `f`, `f'` proper and
horizontal maps `g`, `g'` separated and locally quasi-finite, and let the
second square be the base change by `b`. For a ring `Λ` and
`K` in `D(X'_étale, Λ)` the outer rectangle of the resulting `2×3` diagram
in `D(Y₁_étale, Λ)` commutes, with vertical arrows the comparisons of
Lemma 63.8.1 and horizontal arrows the base change maps of Étale Cohomology,
Section 59.86 and of Lemma 63.3.12. -/
@[stacks 0F7F]
theorem etaleDerivedLowerShriekPushforward_baseChange
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f₁ Λ).Additive]
    [(etaleModulePushforward f'₁ Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ).Additive]
    [(lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback b Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ etaleModuleSheafPullback b' Λ).Additive]
    [(etaleModuleSheafPullback a Λ ⋙ etaleModulePushforward f₁ Λ).Additive]
    [(etaleModuleSheafPullback a' Λ ⋙ etaleModulePushforward f'₁ Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
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
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X' Λ) :
    CommSq
      ((etaleDerivedLowerShriekPushforward_baseChange_top
          g f' Λ b b' a' f'₁ g₁ h_Y' h_X').app K)
      ((etaleDerivedLowerShriekPushforward_baseChange_leftVertical
          f g f' g' Λ b h_sq).app K)
      ((etaleDerivedLowerShriekPushforward_baseChange_rightVertical
          Λ a' f₁ f'₁ g₁ g'₁ h_sq₁).app K)
      ((etaleDerivedLowerShriekPushforward_baseChange_bottom
          f g' Λ b a a' f₁ g'₁ h_X h_back).app K) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
