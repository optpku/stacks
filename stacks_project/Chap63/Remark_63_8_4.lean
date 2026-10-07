module

public import Mathlib.CategoryTheory.Functor.TwoSquare
public import stacks_project.Chap63.Lemma_63_8_1_Comparison

/-!
# Interchange of derived lower shriek / proper pushforward comparisons

Remark 63.8.4: in a 2×2 grid of commutative scheme squares with proper
vertical maps and separated locally quasi-finite horizontal maps, the two
ways of pasting the four Lemma 63.8.1 comparisons agree.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open scoped CategoryTheory.TwoSquare

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X'' X' X Y'' Y' Y Z'' Z' Z : Scheme.{u}}
variable (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
variable (g'' : Y'' ⟶ Z'') (g' : Y' ⟶ Z') (g : Y ⟶ Z)
variable (k' : X'' ⟶ X') (k : X' ⟶ X)
variable (l' : Y'' ⟶ Y') (l : Y' ⟶ Y)
variable (m' : Z'' ⟶ Z') (m : Z' ⟶ Z)
variable (hA : CommSq k' f'' f' l') (hB : CommSq k f' f l)
variable (hC : CommSq l' g'' g' m') (hD : CommSq l g' g m)
variable [IsProper f] [IsProper f'] [IsProper f'']
variable [IsProper g] [IsProper g'] [IsProper g'']
variable [IsSeparated k] [LocallyQuasiFinite k] [LocallyOfFiniteType k]
variable [IsSeparated k'] [LocallyQuasiFinite k'] [LocallyOfFiniteType k']
variable [IsSeparated l] [LocallyQuasiFinite l] [LocallyOfFiniteType l]
variable [IsSeparated l'] [LocallyQuasiFinite l'] [LocallyOfFiniteType l']
variable [IsSeparated m] [LocallyQuasiFinite m] [LocallyOfFiniteType m]
variable [IsSeparated m'] [LocallyQuasiFinite m'] [LocallyOfFiniteType m']
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
variable [Z''.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X''.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y''.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z''.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
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
variable [Z''.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
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
variable [∀ U : Z''.Etale,
  HasWeakSheafify (Z''.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z'.Etale,
  HasWeakSheafify (Z'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z''.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Remark 63.8.4: in a commutative 2×2 grid of scheme squares with proper
vertical maps `f`, `f'`, `f''`, `g`, `g'`, `g''` and separated locally
quasi-finite horizontal maps `k`, `k'`, `l`, `l'`, `m`, `m'`, the two
`TwoSquare` pastings of the four Lemma 63.8.1 comparisons agree.
Scheme-vertical rectangles A+C and B+D are pasted by `≫ₕ`; scheme-horizontal
rectangles A+B and C+D are pasted by `≫ᵥ`. Thus the two maps
`m_! ∘ m'_! ∘ g''_* ∘ f''_* ⟶ g_* ∘ f_* ∘ k_! ∘ k'_!` coincide. -/
@[stacks 0F7E]
theorem etaleDerivedLowerShriekPushforward_interchange
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f'' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward g'' Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule l' Λ).Additive]
    [(lowerShriekModule k' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward g'' Λ ⋙ lowerShriekModule m' Λ).Additive]
    [(lowerShriekModule l' Λ ⋙ etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ).Additive]
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
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g'' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule l' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k' Λ ⋙ etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
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
        (etaleModulePushforward g'' Λ ⋙ lowerShriekModule m' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l' Λ ⋙ etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    (TwoSquare.mk _ _ _ _
        (etaleDerivedLowerShriekPushforward f' f'' l' k' hA Λ) ≫ₕ
      TwoSquare.mk _ _ _ _
        (etaleDerivedLowerShriekPushforward g' g'' m' l' hC Λ)) ≫ᵥ
      (TwoSquare.mk _ _ _ _
          (etaleDerivedLowerShriekPushforward f f' l k hB Λ) ≫ₕ
        TwoSquare.mk _ _ _ _
          (etaleDerivedLowerShriekPushforward g g' m l hD Λ)) =
      (TwoSquare.mk _ _ _ _
          (etaleDerivedLowerShriekPushforward f' f'' l' k' hA Λ) ≫ᵥ
        TwoSquare.mk _ _ _ _
          (etaleDerivedLowerShriekPushforward f f' l k hB Λ)) ≫ₕ
        (TwoSquare.mk _ _ _ _
            (etaleDerivedLowerShriekPushforward g' g'' m' l' hC Λ) ≫ᵥ
          TwoSquare.mk _ _ _ _
            (etaleDerivedLowerShriekPushforward g g' m l hD Λ)) :=
  sorry

/-- The squares A and D meet in a single vertex, so the whiskered natural
transformations of those squares interchange. -/
theorem etaleDerivedLowerShriekPushforward_interchange_square
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f'' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward g'' Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule l' Λ).Additive]
    [(lowerShriekModule k' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward g'' Λ ⋙ lowerShriekModule m' Λ).Additive]
    [(lowerShriekModule l' Λ ⋙ etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ).Additive]
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
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g'' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule l' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k' Λ ⋙ etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
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
        (etaleModulePushforward g'' Λ ⋙ lowerShriekModule m' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l' Λ ⋙ etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    whiskerLeft (etaleDerivedPushforward f'' ⋙ lowerShriekModuleDerived l' Λ)
        (etaleDerivedLowerShriekPushforward g g' m l hD Λ) ≫
      whiskerRight (etaleDerivedLowerShriekPushforward f' f'' l' k' hA Λ)
        (lowerShriekModuleDerived l Λ ⋙ etaleDerivedPushforward g) =
      whiskerRight (etaleDerivedLowerShriekPushforward f' f'' l' k' hA Λ)
          (etaleDerivedPushforward g' ⋙ lowerShriekModuleDerived m Λ) ≫
        whiskerLeft (lowerShriekModuleDerived k' Λ ⋙ etaleDerivedPushforward f')
          (etaleDerivedLowerShriekPushforward g g' m l hD Λ) :=
  sorry

/-- Objectwise form of `etaleDerivedLowerShriekPushforward_interchange` at
`K : D(X''_étale, Λ)`. -/
theorem etaleDerivedLowerShriekPushforward_interchange_app
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f'' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward g'' Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule l' Λ).Additive]
    [(lowerShriekModule k' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward g'' Λ ⋙ lowerShriekModule m' Λ).Additive]
    [(lowerShriekModule l' Λ ⋙ etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ).Additive]
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
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g'' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule l' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k' Λ ⋙ etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
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
        (etaleModulePushforward g'' Λ ⋙ lowerShriekModule m' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l' Λ ⋙ etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
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
    (K : EtaleDerived X'' Λ) :
    ((TwoSquare.mk _ _ _ _
          (etaleDerivedLowerShriekPushforward f' f'' l' k' hA Λ) ≫ₕ
        TwoSquare.mk _ _ _ _
          (etaleDerivedLowerShriekPushforward g' g'' m' l' hC Λ)) ≫ᵥ
        (TwoSquare.mk _ _ _ _
            (etaleDerivedLowerShriekPushforward f f' l k hB Λ) ≫ₕ
          TwoSquare.mk _ _ _ _
            (etaleDerivedLowerShriekPushforward g g' m l hD Λ))).natTrans.app K =
      ((TwoSquare.mk _ _ _ _
            (etaleDerivedLowerShriekPushforward f' f'' l' k' hA Λ) ≫ᵥ
          TwoSquare.mk _ _ _ _
            (etaleDerivedLowerShriekPushforward f f' l k hB Λ)) ≫ₕ
          (TwoSquare.mk _ _ _ _
              (etaleDerivedLowerShriekPushforward g' g'' m' l' hC Λ) ≫ᵥ
            TwoSquare.mk _ _ _ _
              (etaleDerivedLowerShriekPushforward g g' m l hD Λ))).natTrans.app
        K :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
