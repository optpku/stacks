/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.Transitivity
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Category.ULift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CoefficientEquivalence

/-! # Reindexing algebraic-space cotangent complexes on an enlarged étale site -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex ComplexShape
open SheafOfModules.RingedSite
open scoped Simplicial

set_option backward.privateInPublic true

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent.SiteTransport

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The topology on the enlarged small étale site induced by the forgetful equivalence. -/
abbrev siteTopology : GrothendieckTopology (AsSmall.{u + 1} (smallEtaleSite X)) :=
  (AsSmall.down.{u, u + 1, u + 1}).inducedTopology (smallEtaleTopology X)

/-- The forgetful functor of the enlarged site is an equivalence. -/
instance down_isEquivalence :
    (AsSmall.down.{u, u + 1, u + 1} (C := smallEtaleSite X)).IsEquivalence :=
  inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1}
    (C := smallEtaleSite X)).inverse.IsEquivalence)

/-- The enlarged site is a dense presentation of the native étale site. -/
instance down_isDenseSubsite :
    (AsSmall.equiv.{u, u + 1, u + 1} (C := smallEtaleSite X)).inverse.IsDenseSubsite
      (siteTopology X) (smallEtaleTopology X) := by
  change (AsSmall.down.{u, u + 1, u + 1}).IsDenseSubsite
    ((AsSmall.down.{u, u + 1, u + 1}).inducedTopology (smallEtaleTopology X))
    (smallEtaleTopology X)
  infer_instance

/-- The inverse equivalence is continuous for the induced topology. -/
instance down_isContinuous :
    (AsSmall.equiv.{u, u + 1, u + 1} (C := smallEtaleSite X)).symm.functor.IsContinuous
      (siteTopology X) (smallEtaleTopology X) :=
  inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1}
    (C := smallEtaleSite X)).inverse.IsContinuous (siteTopology X) (smallEtaleTopology X))

/-- The forward equivalence is continuous for the induced topology. -/
instance up_isContinuous :
    (AsSmall.equiv.{u, u + 1, u + 1} (C := smallEtaleSite X)).symm.inverse.IsContinuous
      (smallEtaleTopology X) (siteTopology X) :=
  inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1}
    (C := smallEtaleSite X)).functor.IsContinuous (smallEtaleTopology X) (siteTopology X))

/-- Reindexing commutative-ring sheaves on the enlarged étale site preserves coefficients. -/
def ringReindex : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} ⥤
    Sheaf (siteTopology X) CommRingCat.{u + 1} :=
  ((AsSmall.equiv.{u, u + 1, u + 1} :
    smallEtaleSite X ≌ AsSmall.{u + 1} (smallEtaleSite X)).sheafCongr
    (smallEtaleTopology X) (siteTopology X) CommRingCat.{u + 1}).functor

/-- Reindexing module sheaves along the enlarged étale-site equivalence. -/
def moduleEquivalence (B : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) :
    SheafOfModules.{u + 1} (ringOf B) ≌
      SheafOfModules.{u + 1}
        (ringSheaf.{u + 1, u + 1, u + 1} (siteTopology X) ((ringReindex X).obj B)) :=
  SheafOfModules.CoefficientEquivalence.equivalence
    (AsSmall.equiv.{u, u + 1, u + 1} :
      smallEtaleSite X ≌ AsSmall.{u + 1} (smallEtaleSite X)).symm
    (ObjectProperty.isoMk _ (Iso.refl _))

/-- Reindexing module morphisms is additive. -/
instance moduleEquivalence_additive (B : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) :
    (moduleEquivalence X B).functor.Additive where
  map_add := by intros; rfl

/-- Evaluation sends each enlarged-site generator to the native generator of the same section. -/
private def freeCompare (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) :
    CategoryTheory.Sheaf.FreeAlgebra.Presentation.obj ((ringReindex X).obj A)
        ((Under.post (ringReindex X)).obj B) ⟶
      (Under.post (ringReindex X)).obj (CategoryTheory.Sheaf.FreeAlgebra.Presentation.obj A B) :=
  CategoryTheory.Sheaf.FreeAlgebra.evaluation
    ((Under.post (ringReindex X)).obj (CategoryTheory.Sheaf.FreeAlgebra.Presentation.obj A B)) _
    (ObjectProperty.homMk
      ((AsSmall.down.{u, u + 1, u + 1}).op.whiskerLeft
        (CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A B).hom))

/-- Reindexing identifies the free algebra on the unchanged section generators. -/
private theorem freeCompare_isIso (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) : IsIso (freeCompare X A B) := sorry

/-- The enlarged free-algebra comonad endofunctor. -/
private abbrev enlargedFree (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) :=
  (SheafOfModules.RingedSite.CotangentComplex.freeForgetAdjunction
    ((ringReindex X).obj A)).toComonad.toFunctor

/-- Iterated free-algebra comparison starts at the identity and evaluates unchanged generators. -/
private def resolutionIter (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) : (k : ℕ) →
    ((Endofunctor.iterate (enlargedFree X A) k).obj ((Under.post (ringReindex X)).obj B) ⟶
      (Under.post (ringReindex X)).obj ((Endofunctor.iterate (freeForgetEndo A) k).obj B)) :=
  Nat.rec (𝟙 _) (fun k cmp ↦
    (enlargedFree X A).map cmp ≫
      freeCompare X A ((Endofunctor.iterate (freeForgetEndo A) k).obj B))

/-- Standard-resolution terms compare by the recursively evaluated free generators. -/
private def resolutionCompare (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :
    SheafOfModules.RingedSite.CotangentComplex.standardTerm ((ringReindex X).obj A)
        ((Under.post (ringReindex X)).obj B) n ⟶
      (Under.post (ringReindex X)).obj (standardTerm A B n) :=
  eqToHom (Comonad.simplicialResolution.eval.degree
    (SheafOfModules.RingedSite.CotangentComplex.freeForgetAdjunction
      ((ringReindex X).obj A)).toComonad ((Under.post (ringReindex X)).obj B) n.unop.len) ≫
    resolutionIter X A B (n.unop.len + 1)

/-- Resolution comparison preserves augmentations and every simplicial operator. -/
private theorem resolutionCompare_laws
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) (B : Under A) :
    (∀ n, (resolutionCompare X A B n).right ≫
      (ringReindex X).map (standardAugmentation A B n) =
        SheafOfModules.RingedSite.CotangentComplex.standardAugmentation
          ((ringReindex X).obj A) ((Under.post (ringReindex X)).obj B) n) ∧
    (∀ {n m} (f : n ⟶ m),
      (SheafOfModules.RingedSite.CotangentComplex.standardMap
        ((ringReindex X).obj A) ((Under.post (ringReindex X)).obj B) f).right ≫
          (resolutionCompare X A B m).right =
        (resolutionCompare X A B n).right ≫ (ringReindex X).map (standardMap A B f).right) := sorry

/-- The homogeneous standard-resolution term on the enlarged site. -/
private abbrev enlargedTerm (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :=
  SheafOfModules.RingedSite.CotangentComplex.standardTerm ((ringReindex X).obj A)
    ((Under.post (ringReindex X)).obj B) n

/-- Native differentials reindexed on the enlarged site and restricted along resolution comparison. -/
private abbrev differentialTarget (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :=
  (restrictionAlong (resolutionCompare X A B n).right).obj
    ((moduleEquivalence X (standardTerm A B n).right).functor.obj
      (differentialsOn (standardTerm A B n).hom))

/-- The additive differential assignment sends `q` to the native differential of its resolution image. -/
private def differentialValue (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) (n : SimplexCategoryᵒᵖ)
    (V : (AsSmall.{u + 1} (smallEtaleSite X))ᵒᵖ) :
    (enlargedTerm X A B n).right.obj.obj V →+ (differentialTarget X A B n).val.obj V :=
  ((relativeDifferential.{u + 1, u, u + 1} (standardTerm A B n).hom).d
    (X := (AsSmall.down.{u, u + 1, u + 1}).op.obj V)).comp
      ((resolutionCompare X A B n).right.hom.app V).hom.toAddMonoidHom

/-- The reindexed native differential satisfies the Leibniz, restriction, and relative-base laws. -/
private theorem differentialsCompare_laws
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    (∀ V (a b : (enlargedTerm X A B n).right.obj.obj V),
      differentialValue X A B n V (a * b) =
        a • differentialValue X A B n V b + b • differentialValue X A B n V a) ∧
    (∀ {V W} (f : V ⟶ W) (a : (enlargedTerm X A B n).right.obj.obj V),
      differentialValue X A B n W ((enlargedTerm X A B n).right.obj.map f a) =
        (differentialTarget X A B n).val.map f (differentialValue X A B n V a)) ∧
    (∀ V (a : ((ringReindex X).obj A).obj.obj V),
      differentialValue X A B n V ((enlargedTerm X A B n).hom.hom.app V a) = 0) := sorry

/-- Universal descent of the native differential composed with resolution comparison. -/
private def differentialsCompare (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials.{u + 1, u + 1, u + 1} (enlargedTerm X A B n).hom ⟶
      differentialTarget X A B n :=
  relativeDifferentialDesc.{u + 1, u + 1, u + 1} (enlargedTerm X A B n).hom
    { d := fun {V} ↦ differentialValue X A B n V
      d_mul := (differentialsCompare_laws X A B n).1 _
      d_map := (differentialsCompare_laws X A B n).2.1
      d_app := (differentialsCompare_laws X A B n).2.2 _ }

/-- The augmentation of the homogeneous enlarged resolution. -/
private abbrev enlargedAugmentation (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :=
  SheafOfModules.RingedSite.CotangentComplex.standardAugmentation
    ((ringReindex X).obj A) ((Under.post (ringReindex X)).obj B) n

/-- The native extension-of-scalars unit for a standard-resolution term. -/
private abbrev nativeTensorUnit (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :=
  (extendRestrictAdj (standardAugmentation A B n)).unit.app
    (differentialsOn (standardTerm A B n).hom)

/-- The native scalar-extension unit, reindexed and restricted through resolution comparison. -/
private def tensorUnitCompare (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :
    differentialTarget X A B n ⟶
      (restrictionAlong (enlargedAugmentation X A B n)).obj
        ((moduleEquivalence X B.right).functor.obj ((simplicialModule A B).obj n)) where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        (X := (differentialTarget X A B n).val.obj V)
        (Y := ((restrictionAlong (enlargedAugmentation X A B n)).obj
          ((moduleEquivalence X B.right).functor.obj ((simplicialModule A B).obj n))).val.obj V)
        { toFun := fun x ↦ (nativeTensorUnit X A B n).val.app
            ((AsSmall.down.{u, u + 1, u + 1}).op.obj V) x
          map_add' := fun x y ↦ ((nativeTensorUnit X A B n).val.app _).hom.map_add x y
          map_smul' := by
            intro r x
            have h := congrArg (fun f ↦ (f.hom.app V).hom r)
              ((resolutionCompare_laws X A B).1 n)
            have linear := ((nativeTensorUnit X A B n).val.app
              ((AsSmall.down.{u, u + 1, u + 1}).op.obj V)).hom.map_smul
                (((resolutionCompare X A B n).right.hom.app V).hom r) x
            exact linear.trans (congrArg
              (fun b : (ringOf B.right).obj.obj ((AsSmall.down.{u, u + 1, u + 1}).op.obj V) ↦
                @SMul.smul _ (((simplicialModule A B).obj n).val.obj
                  ((AsSmall.down.{u, u + 1, u + 1}).op.obj V)) inferInstance b
                    ((nativeTensorUnit X A B n).val.app _ x)) h) }
      naturality := by
        intro V W f
        ext x
        exact congrArg (fun g ↦ g.hom x)
          ((nativeTensorUnit X A B n).val.naturality
            ((AsSmall.down.{u, u + 1, u + 1}).op.map f)) }

/-- Scalar extension of the differential comparison by its genuine adjunction. -/
private def tensorCompare (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :
    (SheafOfModules.RingedSite.CotangentComplex.simplicialModule.{u + 1}
      ((ringReindex X).obj A) ((Under.post (ringReindex X)).obj B)).obj n ⟶
      (moduleEquivalence X B.right).functor.obj ((simplicialModule A B).obj n) :=
  ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap.{u + 1, u + 1, u + 1} (enlargedAugmentation X A B n))).homEquiv
      (relativeDifferentials.{u + 1, u + 1, u + 1} (enlargedTerm X A B n).hom)
      ((moduleEquivalence X B.right).functor.obj ((simplicialModule A B).obj n))).symm
      (differentialsCompare X A B n ≫ tensorUnitCompare X A B n)

/-- The scalar-extended differential comparisons commute with all simplicial operators. -/
private theorem tensorCompare_naturality
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (SheafOfModules.RingedSite.CotangentComplex.simplicialModule.{u + 1}
      ((ringReindex X).obj A) ((Under.post (ringReindex X)).obj B)).map f ≫
        tensorCompare X A B m =
      tensorCompare X A B n ≫ (moduleEquivalence X B.right).functor.map
        ((simplicialModule A B).map f) := sorry

/-- The native cotangent cochain complex reindexed by the module equivalence. -/
private abbrev reindexedCochain {A B : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  ((moduleEquivalence X B).functor.mapHomologicalComplex (up ℤ)).obj (cotangentCochainObj φ)

/-- In nonpositive degrees, cotangent comparison is scalar-extended universal differentiation. -/
private def negativeComponent {A B : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (n : ℕ) :
    (SheafOfModules.RingedSite.CotangentComplex.obj ((ringReindex X).obj A)
      (Under.mk ((ringReindex X).map φ))).X (-n) ⟶ (reindexedCochain X φ).X (-n) :=
  (SheafOfModules.RingedSite.CotangentComplex.objXIso ((ringReindex X).obj A)
    (Under.mk ((ringReindex X).map φ)) n).hom ≫
      tensorCompare X A (Under.mk φ) (op ⦋n⦌) ≫
        (moduleEquivalence X B).functor.map (cotangentXIso φ n).inv

/-- Cotangent comparison uses the resolution comparison in nonpositive degrees and zero otherwise. -/
private def comparisonComponent {A B : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (i : ℤ) :
    (SheafOfModules.RingedSite.CotangentComplex.obj ((ringReindex X).obj A)
      (Under.mk ((ringReindex X).map φ))).X i ⟶ (reindexedCochain X φ).X i :=
  match i with
  | Int.ofNat 0 => negativeComponent X φ 0
  | Int.ofNat (n + 1) => 0
  | Int.negSucc n => negativeComponent X φ (n + 1)

/-- Cotangent comparison commutes with the cochain differentials. -/
private theorem comparison_comm {A B : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    comparisonComponent X φ i ≫ (reindexedCochain X φ).d i j =
      (SheafOfModules.RingedSite.CotangentComplex.obj ((ringReindex X).obj A)
        (Under.mk ((ringReindex X).map φ))).d i j ≫ comparisonComponent X φ j := sorry

/-- The enlarged homogeneous cotangent complex maps canonically to the reindexed native complex. -/
def comparison {A B : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    SheafOfModules.RingedSite.CotangentComplex.obj ((ringReindex X).obj A)
        (Under.mk ((ringReindex X).map φ)) ⟶
      ((moduleEquivalence X B).functor.mapHomologicalComplex (up ℤ)).obj
        (cotangentCochainObj φ) where
  f := comparisonComponent X φ
  comm' := comparison_comm X φ

/-- The canonical comparison with the reindexed native cotangent complex is invertible. -/
instance comparison_isIso {A B : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (φ : A ⟶ B) : IsIso (comparison X φ) := sorry

/-- Enlarging the étale site without changing coefficients identifies its cotangent complexes. -/
def iso {A B : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    SheafOfModules.RingedSite.CotangentComplex.obj ((ringReindex X).obj A)
        (Under.mk ((ringReindex X).map φ)) ≅
      ((moduleEquivalence X B).functor.mapHomologicalComplex (up ℤ)).obj
        (cotangentCochainObj φ) :=
  asIso (comparison X φ)

/-- The forward map of the site transport is its canonical comparison. -/
theorem iso_hom {A B : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    (iso X φ).hom = comparison X φ := rfl

end AlgebraicGeometry.AlgebraicSpace.Cotangent.SiteTransport
