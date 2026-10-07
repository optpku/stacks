module

public import stacks_project.Chap63.Lemma_63_8_3_Comp
public import stacks_project.Chap63.Lemma_63_8_3_Comparison

/-!
# Horizontal composition of derived lower shriek / proper pushforward comparisons

Lemma 63.8.3: the Lemma 63.8.1 comparisons of two horizontally adjacent
squares compose, after the Lemma 63.3.13 identifications of lower shriek, to
the comparison of the outer rectangle.
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

variable {X'' X' X Y'' Y' Y : Scheme.{u}}
variable (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
variable (g' : X'' ⟶ X') (g : X' ⟶ X) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
variable (h_left : CommSq g' f'' f' h') (h_right : CommSq g f' f h)
variable [IsProper f] [IsProper f'] [IsProper f'']
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [IsSeparated g'] [LocallyQuasiFinite g'] [LocallyOfFiniteType g']
variable [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h]
variable [IsSeparated h'] [LocallyQuasiFinite h'] [LocallyOfFiniteType h']
variable (Λ : Type u) [CommRing Λ]
variable [X''.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y''.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X''.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y''.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [X''.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y''.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X''.Etale,
  HasWeakSheafify (X''.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y''.Etale,
  HasWeakSheafify (Y''.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Lemma 63.8.3: for a horizontally pasted pair of commutative squares of
schemes with proper vertical maps and separated locally quasi-finite
horizontal maps, the Lemma 63.8.1 comparisons of the two squares compose,
after the identifications `(h' ≫ h)_! ≅ h'_! ⋙ h_!` and
`(g' ≫ g)_! ≅ g'_! ⋙ g_!`, to the comparison of the outer rectangle. -/
@[stacks 0F7D]
theorem etaleDerivedLowerShriekPushforward_horiz_comp
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f'' Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule h' Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule h Λ).Additive]
    [(lowerShriekModule g Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule (h' ≫ h) Λ).Additive]
    [(lowerShriekModule (g' ≫ g) Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule h' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule (h' ≫ h) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule (g' ≫ g) Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedLowerShriekPushforwardHoriz
        f'' f' f g' g h' h h_left h_right Λ =
      etaleDerivedLowerShriekPushforward_horizOuter
        f'' f' f g' g h' h h_left h_right Λ :=
  sorry

/-- Objectwise form of `etaleDerivedLowerShriekPushforward_horiz_comp` at
`K : D(X''_étale, Λ)`. -/
theorem etaleDerivedLowerShriekPushforward_horiz_comp_app
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f'' Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule h' Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule h Λ).Additive]
    [(lowerShriekModule g Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule (h' ≫ h) Λ).Additive]
    [(lowerShriekModule (g' ≫ g) Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule h' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule (h' ≫ h) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule (g' ≫ g) Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X'' Λ) :
    (etaleDerivedLowerShriekPushforwardHoriz
        f'' f' f g' g h' h h_left h_right Λ).app K =
      (etaleDerivedLowerShriekPushforward_horizOuter
        f'' f' f g' g h' h h_left h_right Λ).app K :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
