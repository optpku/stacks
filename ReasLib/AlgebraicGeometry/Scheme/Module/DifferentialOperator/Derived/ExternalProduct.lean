/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.ExternalTensor

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kunneth

/-- The ordinary total external-product complex attached to an explicit external-product
functor on finite-order differential operators. -/
noncomputable abbrev externalTotalComplex {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms]
    [∀ F, (T.obj F).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] :=
  HomologicalComplex.mapBifunctor F G T (up ℤ)

/-- In bidegree `(i, j)`, the external-product functor has the ordinary scheme external tensor
product as its underlying quasicoherent module. -/
theorem externalTotalComplex_obj_eq {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms]
    [∀ F, (T.obj F).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] (i j : ℤ) :
    Hom.FiniteOrderDifferentialOperatorCat.underlying (pullback.fst a b ≫ a)
        ((T.obj (F.X i)).obj (G.X j)) =
      Scheme.Modules.externalTensorProduct a b
        (Hom.FiniteOrderDifferentialOperatorCat.underlying a (F.X i))
        (Hom.FiniteOrderDifferentialOperatorCat.underlying b (G.X j)) := sorry

/-- The canonical tensor comparison from coefficient restrictions to the coefficient
restriction of the tensor product. -/
noncomputable def coefficientTensorComparison {Z S : Scheme.{u}} (f : Z ⟶ S)
    (M N : Z.Modules) :
    MonoidalCategory.tensorObj
        ((restrictionAlong
          (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)).obj M)
        ((restrictionAlong
          (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)).obj N) ⟶
      (restrictionAlong
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)).obj
        (MonoidalCategory.tensorObj M N) :=
  (ModuleSheafification.tensorObjIso
      (RingedSpace.DeRham.coefficients f.toShHom)
      ((restrictionAlong
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)).obj M)
      ((restrictionAlong
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)).obj N)).hom ≫
    ModuleSheafification.mapToRestriction
      (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)
      (PresheafOfModules.Restriction.tensorComparison
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f).hom M.val N.val) ≫
    (restrictionAlong
      (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)).map
        (ModuleSheafification.tensorObjIso Z.𝒪 M N).inv

/-- The coefficient tensor comparison is the sheafification of the sectionwise restriction
comparison followed by the ordinary tensor sheafification isomorphism. -/
theorem coefficientTensorComparison_def {Z S : Scheme.{u}} (f : Z ⟶ S)
    (M N : Z.Modules) :
    coefficientTensorComparison f M N =
      (ModuleSheafification.tensorObjIso
        (RingedSpace.DeRham.coefficients f.toShHom)
        ((restrictionAlong
          (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)).obj M)
        ((restrictionAlong
          (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)).obj N)).hom ≫
      ModuleSheafification.mapToRestriction
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)
        (PresheafOfModules.Restriction.tensorComparison
          (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f).hom M.val N.val) ≫
      (restrictionAlong
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap f)).map
          (ModuleSheafification.tensorObjIso Z.𝒪 M N).inv := sorry

/-- The canonical bidegree map from the tensor of coefficient pullbacks to the coefficient
realization of the ordinary external product. -/
noncomputable def externalComparisonBidegree {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ) (i j : ℤ) :
    ((MonoidalCategory.curriedTensor (RingedSpace.DeRham.Modules
      (pullback.fst a b ≫ a).toShHom)).obj
        ((leftPullbackComplex a b F).X i)).obj
      ((rightPullbackComplex a b G).X j) ⟶
        (Hom.FiniteOrderDifferentialOperatorCat.toCoefficientModules
          (pullback.fst a b ≫ a)).obj ((T.obj (F.X i)).obj (G.X j)) :=
  (leftPullbackComparison a b
      (Hom.FiniteOrderDifferentialOperatorCat.underlying a (F.X i)) ⊗ₘ
    rightPullbackComparison a b
      (Hom.FiniteOrderDifferentialOperatorCat.underlying b (G.X j))) ≫
    coefficientTensorComparison (pullback.fst a b ≫ a)
      ((Scheme.Modules.pullback (pullback.fst a b)).obj
        (Hom.FiniteOrderDifferentialOperatorCat.underlying a (F.X i)))
      ((Scheme.Modules.pullback (pullback.snd a b)).obj
        (Hom.FiniteOrderDifferentialOperatorCat.underlying b (G.X j))) ≫
    (restrictionAlong
      (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap
        (pullback.fst a b ≫ a))).map
      (eqToHom (hT.obj_eq (F.X i) (G.X j)).symm)

/-- The degree-`n` component of the comparison from the coefficient tensor total to the
ordinary external-product total. -/
noncomputable def externalComparisonComponent {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms]
    [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] (n : ℤ) :
    (coefficientTensorComplex a b F G).X n ⟶
      ((Hom.FiniteOrderDifferentialOperatorCat.toCoefficientComplex
        (pullback.fst a b ≫ a)).obj (externalTotalComplex a b T hT F G)).X n :=
  HomologicalComplex.mapBifunctorDesc
    (fun i j hij ↦ externalComparisonBidegree a b T hT F G i j ≫
      (Hom.FiniteOrderDifferentialOperatorCat.toCoefficientModules
        (pullback.fst a b ≫ a)).map
          (HomologicalComplex.ιMapBifunctor F G T (up ℤ) i j n hij))

/-- The degreewise external-product comparisons commute with the total differentials. -/
theorem externalComparisonComponent_comm {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms]
    [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)]
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    externalComparisonComponent a b T hT F G i ≫
        ((Hom.FiniteOrderDifferentialOperatorCat.toCoefficientComplex
          (pullback.fst a b ≫ a)).obj
            (externalTotalComplex a b T hT F G)).d i j =
      (coefficientTensorComplex a b F G).d i j ≫
        externalComparisonComponent a b T hT F G j := sorry

/-- The canonical chain map from the coefficient tensor total to `Tot(F ⊠ G)`. -/
noncomputable def externalComparison {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms]
    [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] :
    coefficientTensorComplex a b F G ⟶
      (Hom.FiniteOrderDifferentialOperatorCat.toCoefficientComplex
        (pullback.fst a b ≫ a)).obj (externalTotalComplex a b T hT F G) :=
  HomologicalComplex.Hom.mk (externalComparisonComponent a b T hT F G)
    (externalComparisonComponent_comm a b T hT F G)

/-- The chain comparison has the prescribed degreewise component. -/
theorem externalComparison_f {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms]
    [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] (n : ℤ) :
    (externalComparison a b T hT F G).f n =
      externalComparisonComponent a b T hT F G n := sorry

/-- The derived coefficient object represented by the ordinary total external-product
complex `Tot(F ⊠ G)`. -/
noncomputable abbrev externalTotal {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms]
    [∀ F, (T.obj F).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] :
    CoefficientDerived (pullback.fst a b ≫ a) :=
  coefficientObject (pullback.fst a b ≫ a) (externalTotalComplex a b T hT F G)

/-- `externalTotal` is the localization of the coefficient realization of
`externalTotalComplex`. -/
theorem externalTotal_def {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms]
    [∀ F, (T.obj F).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] :
    externalTotal a b T hT F G =
      coefficientObject (pullback.fst a b ≫ a) (externalTotalComplex a b T hT F G) := sorry

end AlgebraicGeometry.Scheme.Modules.Kunneth

end
