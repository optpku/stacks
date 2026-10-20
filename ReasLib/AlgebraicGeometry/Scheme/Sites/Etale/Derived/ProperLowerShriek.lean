module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.ProperPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst

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

/-- The iterated cochain unit for `Rf'_* ⋙ g_!`, using exactness of `g_!`. -/
def etaleDerivedLowerShriekPushforward_leftUnit
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ) ⟶
      DerivedCategory.Q ⋙
        (etaleDerivedPushforward f' ⋙ lowerShriekModuleDerived g Λ) :=
  (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
        (ComplexShape.up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).hom ≫
    (Functor.associator
      ((etaleModulePushforward f' Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      ((lowerShriekModule g Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).hom ≫
    whiskerLeft
      ((etaleModulePushforward f' Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (lowerShriekModule g Λ).mapDerivedCategoryFactors.inv ≫
    (Functor.associator
      ((etaleModulePushforward f' Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)))
      (lowerShriekModuleDerived g Λ)).inv ≫
    whiskerRight
      (RightDerived.Cochain.unit (etaleModulePushforward f' Λ))
      (lowerShriekModuleDerived g Λ) ≫
    (Functor.associator
      (DerivedCategory.Q :
        CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
      (etaleDerivedPushforward f')
      (lowerShriekModuleDerived g Λ)).hom

/-- Exactness of `g_!` makes `Rf'_* ⋙ g_!` a right-derived functor of
`f'_* ⋙ g_!`. -/
instance etaleDerivedLowerShriekPushforward_left_isRightDerived
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    (etaleDerivedPushforward f' ⋙ lowerShriekModuleDerived g Λ).IsRightDerivedFunctor
      (etaleDerivedLowerShriekPushforward_leftUnit f' g Λ)
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  sorry

/-- The derived identification `g_! ∘ Rf'_* ≅ R(g_! ∘ f'_*)`. -/
def etaleDerivedLowerShriekPushforward_leftIso
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f' ⋙ lowerShriekModuleDerived g Λ ≅
      RightDerived.Cochain.functor
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (etaleDerivedLowerShriekPushforward_leftUnit f' g Λ)
    (RightDerived.Cochain.unit
      (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
    (Iso.refl _)

/-- The sheaf-level module isomorphism transported to total right-derived
functors. -/
def etaleDerivedLowerShriekPushforward_middleIso
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.functor
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ) ≅
      RightDerived.Cochain.functor
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (RightDerived.Cochain.unit
      (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
    (RightDerived.Cochain.unit
      (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModuleLowerShriekPushforwardIso f f' g g' h_sq Λ)
        (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))

/-- The iterated cochain unit for `R(g'_! ⋙ f_*)`, using exactness of `g'_!`
but not injective-preservation. -/
def etaleDerivedLowerShriekPushforward_rightUnit
    [(etaleModulePushforward f Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
            DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (lowerShriekModuleDerived g' Λ ⋙ etaleDerivedPushforward f) :=
  RightDerived.Cochain.ExactFirst.unit
    (ExactFunctor.of (lowerShriekModule g' Λ))
    (etaleModulePushforward f Λ)

/-- The iterated unit of `R(g'_! ⋙ f_*)` is the exact-first cochain unit. -/
theorem etaleDerivedLowerShriekPushforward_rightUnit_eq
    [(etaleModulePushforward f Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedLowerShriekPushforward_rightUnit f g' Λ =
      RightDerived.Cochain.ExactFirst.unit
        (ExactFunctor.of (lowerShriekModule g' Λ))
        (etaleModulePushforward f Λ) :=
  rfl

/-- The derived comparison `R(g'_! ⋙ f_*) ⟶ g'_! ⋙ Rf_*`. It is induced by
the exact-first cochain unit. -/
def etaleDerivedLowerShriekPushforward_rightComparison
    [(etaleModulePushforward f Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.functor
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ) ⟶
      lowerShriekModuleDerived g' Λ ⋙ etaleDerivedPushforward f :=
  (RightDerived.Cochain.functor
      (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (lowerShriekModuleDerived g' Λ ⋙ etaleDerivedPushforward f)
    (etaleDerivedLowerShriekPushforward_rightUnit f g' Λ)

/-- The canonical derived comparison `g_! ∘ Rf'_* ⟶ Rf_* ∘ g'_!`. -/
def etaleDerivedLowerShriekPushforward
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
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f' ⋙ lowerShriekModuleDerived g Λ ⟶
      lowerShriekModuleDerived g' Λ ⋙ etaleDerivedPushforward f :=
  (etaleDerivedLowerShriekPushforward_leftIso f' g Λ).hom ≫
    (etaleDerivedLowerShriekPushforward_middleIso f f' g g' h_sq Λ).hom ≫
    etaleDerivedLowerShriekPushforward_rightComparison f g' Λ

/-- The comparison at an object of `D(X'_étale, Λ)`. -/
def etaleDerivedLowerShriekPushforward_app
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
    (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (lowerShriekModuleDerived g Λ).obj ((etaleDerivedPushforward f').obj K) ⟶
      (etaleDerivedPushforward f).obj ((lowerShriekModuleDerived g' Λ).obj K) :=
  (etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K

/-- The objectwise comparison is the component of
`etaleDerivedLowerShriekPushforward`. -/
theorem etaleDerivedLowerShriekPushforward_app_eq
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
    (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) :
    etaleDerivedLowerShriekPushforward_app f f' g g' h_sq Λ K =
      (etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K :=
  rfl

/-- The comparison `g_! Rf'_* K ⟶ Rf_* (g'_! K)` is an
isomorphism if `K` is bounded below and has torsion cohomology sheaves. -/
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
    (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    [DerivedCategory.IsGE K n] :
    IsIso ((etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K) :=
  sorry

/-- The comparison `g_! Rf'_* K ⟶ Rf_* (g'_! K)` is an
isomorphism if `Λ` is a torsion ring. -/
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
    (hΛ : AddMonoid.IsTorsion Λ) (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIso ((etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K) :=
  sorry


end AlgebraicGeometry.Scheme.Etale

end
