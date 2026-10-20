module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ComplexSystem
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The total derived pushforward of cochain complexes of abelian étale sheaves. -/
abbrev etaleAbelianPushforwardDerived {T U : Scheme.{u}} (f : U ⟶ T)
    [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        T.smallEtaleTopology U.smallEtaleTopology).Additive]
    [Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          T.smallEtaleTopology U.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))] :
    DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) :=
  RightDerived.Cochain.functor
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology)

namespace HigherDirectImage

namespace Complex

section Values

variable {T U : Scheme.{u}} (f : U ⟶ T)
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    T.smallEtaleTopology U.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        T.smallEtaleTopology U.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/-- The degree-`p` higher direct image of a cochain complex is homology of its total derived pushforward. -/
def value (K : CochainComplex (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (p : ℤ) :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) p).obj
    ((etaleAbelianPushforwardDerived f).obj (DerivedCategory.Q.obj K))

/-- A morphism of cochain complexes induces a morphism between their derived higher direct images. -/
def map {K L : CochainComplex (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) ℤ}
    (φ : K ⟶ L) (p : ℤ) : value f K p ⟶ value f L p :=
  (DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) p).map
    ((etaleAbelianPushforwardDerived f).map (DerivedCategory.Q.map φ))

end Values

section Squares

variable {S X S' X' : Scheme.{u}}
variable (vertical : X ⟶ S) (vertical' : X' ⟶ S')
variable (top : X' ⟶ X) (bottom : S' ⟶ S)
variable (comm : top ≫ vertical = vertical' ≫ bottom)
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf S'.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf S'.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {T U : Scheme.{u}} (morphism : U ⟶ T)
    (presheaf : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback morphism).op.HasLeftKanExtension presheaf]
variable [∀ {T U : Scheme.{u}} (morphism : U ⟶ T),
    ((smallEtalePullback morphism).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable [((smallEtalePullback vertical).sheafPushforwardContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology X.smallEtaleTopology).Additive]
variable [((smallEtalePullback vertical').sheafPushforwardContinuous AddCommGrpCat.{u}
    S'.smallEtaleTopology X'.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback vertical).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology X.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback vertical').sheafPushforwardContinuous AddCommGrpCat.{u}
        S'.smallEtaleTopology X'.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}) (up ℤ))]

/-- The adjunction mate of a commutative scheme square compares inverse image of pushforward with pushforward of inverse image. -/
def ordinaryBaseChange :
    (smallEtalePullback vertical).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology X.smallEtaleTopology ⋙
      (smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology S'.smallEtaleTopology ⟶
    (smallEtalePullback top).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology X'.smallEtaleTopology ⋙
      (smallEtalePullback vertical').sheafPushforwardContinuous AddCommGrpCat.{u}
        S'.smallEtaleTopology X'.smallEtaleTopology :=
  let inverseSquare := (inverseImageCompIso vertical' bottom) ≪≫
    eqToIso (congrArg
      (fun morphism => (smallEtalePullback morphism).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology X'.smallEtaleTopology) comm.symm) ≪≫
    (inverseImageCompIso top vertical).symm
  ((mateEquiv
    (G := (smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology S'.smallEtaleTopology)
    (H := (smallEtalePullback top).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology X'.smallEtaleTopology)
    ((smallEtalePullback vertical).sheafAdjunctionContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback vertical').sheafAdjunctionContinuous AddCommGrpCat.{u}
      S'.smallEtaleTopology X'.smallEtaleTopology)) inverseSquare.hom).natTrans

/-- The total derivation unit followed by exact inverse image is a comparison from cochain pushforward to pulled-back derived pushforward. -/
def pullbackUnit :
    RightDerived.Cochain.toDerived
        ((smallEtalePullback vertical).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology X.smallEtaleTopology) ⋙
      ((smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology S'.smallEtaleTopology).mapDerivedCategory ⟶
    DerivedCategory.Q ⋙ (etaleAbelianPushforwardDerived vertical ⋙
      ((smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology S'.smallEtaleTopology).mapDerivedCategory) :=
  whiskerRight
      (RightDerived.Cochain.unit
        ((smallEtalePullback vertical).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology X.smallEtaleTopology))
      ((smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology S'.smallEtaleTopology).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- Exact inverse image of total derived pushforward satisfies the right-derived universal property for the whiskered derivation unit. -/
instance pullbackIsRightDerived :
    (etaleAbelianPushforwardDerived vertical ⋙
      ((smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology S'.smallEtaleTopology).mapDerivedCategory).IsRightDerivedFunctor
      (pullbackUnit vertical bottom)
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (up ℤ)) := sorry

/-- Termwise square base change and the forward derivation unit compare cochain pushforward with derived pushforward after inverse image. -/
def baseChangeUnit :
    RightDerived.Cochain.toDerived
        ((smallEtalePullback vertical).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology X.smallEtaleTopology) ⋙
      ((smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology S'.smallEtaleTopology).mapDerivedCategory ⟶
    DerivedCategory.Q ⋙
      (((smallEtalePullback top).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology X'.smallEtaleTopology).mapDerivedCategory ⋙
          etaleAbelianPushforwardDerived vertical') :=
  let push := (smallEtalePullback vertical).sheafPushforwardContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology X.smallEtaleTopology
  let push' := (smallEtalePullback vertical').sheafPushforwardContinuous AddCommGrpCat.{u}
    S'.smallEtaleTopology X'.smallEtaleTopology
  let pullTop := (smallEtalePullback top).sheafPullback AddCommGrpCat.{u}
    X.smallEtaleTopology X'.smallEtaleTopology
  let pullBottom := (smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
    S.smallEtaleTopology S'.smallEtaleTopology
  (Functor.associator _ _ _).hom ≫
    whiskerLeft (push.mapHomologicalComplex (up ℤ)) pullBottom.mapDerivedCategoryFactors.hom ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (push ⋙ pullBottom)) (up ℤ)).hom
      DerivedCategory.Q ≫
    whiskerRight (NatTrans.mapHomologicalComplex
      (ordinaryBaseChange vertical vertical' top bottom comm) (up ℤ)) DerivedCategory.Q ≫
    whiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (pullTop ⋙ push')) (up ℤ)).inv
      DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft (pullTop.mapHomologicalComplex (up ℤ)) (RightDerived.Cochain.unit push') ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight pullTop.mapDerivedCategoryFactors.inv (etaleAbelianPushforwardDerived vertical') ≫
    (Functor.associator _ _ _).hom

/-- Universal descent of the cochain square comparison constructs derived base change for every commutative square of schemes. -/
def derivedBaseChange :
    etaleAbelianPushforwardDerived vertical ⋙
      ((smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology S'.smallEtaleTopology).mapDerivedCategory ⟶
    ((smallEtalePullback top).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology X'.smallEtaleTopology).mapDerivedCategory ⋙
      etaleAbelianPushforwardDerived vertical' :=
  (etaleAbelianPushforwardDerived vertical ⋙
      ((smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology S'.smallEtaleTopology).mapDerivedCategory).rightDerivedDesc
    (pullbackUnit vertical bottom)
    (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (up ℤ))
    _ (baseChangeUnit vertical vertical' top bottom comm)

omit [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [∀ {T U : Scheme.{u}} (morphism : U ⟶ T)
    (presheaf : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback morphism).op.HasLeftKanExtension presheaf] in
/-- Derived square base change recovers the cochain square comparison after precomposition with the derivation unit. -/
theorem derivedBaseChange_fac :
    pullbackUnit vertical bottom ≫ whiskerLeft DerivedCategory.Q
        (derivedBaseChange vertical vertical' top bottom comm) =
      baseChangeUnit vertical vertical' top bottom comm :=
  Functor.rightDerived_fac _ (pullbackUnit vertical bottom)
    (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (up ℤ))
    _ (baseChangeUnit vertical vertical' top bottom comm)

/-- A commutative scheme square induces base change on the higher direct images of a complex in every integral degree. -/
def baseChange (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (p : ℤ) :
    ((smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology S'.smallEtaleTopology).obj (value vertical K p) ⟶
      value vertical'
        (((smallEtalePullback top).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology X'.smallEtaleTopology).mapHomologicalComplex (up ℤ) |>.obj K) p :=
  let pullBottom := (smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
    S.smallEtaleTopology S'.smallEtaleTopology
  let pullTop := (smallEtalePullback top).sheafPullback AddCommGrpCat.{u}
    X.smallEtaleTopology X'.smallEtaleTopology
  (Functor.MapDerivedCategory.homologyFunctorIso pullBottom p).inv.app
      ((etaleAbelianPushforwardDerived vertical).obj (DerivedCategory.Q.obj K)) ≫
    (DerivedCategory.homologyFunctor (Sheaf S'.smallEtaleTopology AddCommGrpCat.{u}) p).map
      ((derivedBaseChange vertical vertical' top bottom comm).app (DerivedCategory.Q.obj K)) ≫
    (DerivedCategory.homologyFunctor (Sheaf S'.smallEtaleTopology AddCommGrpCat.{u}) p).map
      ((etaleAbelianPushforwardDerived vertical').map (pullTop.mapDerivedCategoryFactors.hom.app K))

end Squares

end Complex

end HigherDirectImage

end AlgebraicGeometry.Scheme.Etale

end
