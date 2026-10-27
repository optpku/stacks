/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.DerivedEvaluation
import StacksCheckRecall

/-!
# Computing derived projection lower shriek by the standard polynomial resolution

Evaluation on the functorial standard affine resolution computes fibre homology.
Its sheafification in nonpositive degrees represents derived projection lower shriek.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits AlgebraicTopology
open HomologicalComplex FiberedCategoryOver.FiberHomology Functor.LeftDerived
open scoped AlgebraicGeometry Simplicial

universe u w qS qT

namespace AlgebraicGeometry.Scheme.CotangentSite

/- Remark 92.25.2: the sheafified standard-resolution evaluation complex computes
 the actual total left derived functor of projection lower shriek. -/
@[stacks 08VB] #check (AlgebraicGeometry.Scheme.CotangentSite.evalSheafComplex_computes :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{w}]
    [HasZeroObject (Sheaf X.smallZariskiTopology AddCommGrpCat.{w})]
    [HasSheafify (topology Λ X) AddCommGrpCat.{w}]
    [((forgetZariski Λ X).sheafPushforwardContinuous AddCommGrpCat.{w}
        (topology Λ X) X.smallZariskiTopology).IsRightAdjoint]
    [HasDerivedCategory.{qS} (Sheaf (topology Λ X) AddCommGrpCat.{w})]
    [HasDerivedCategory.{qT} (Sheaf X.smallZariskiTopology AddCommGrpCat.{w})]
    [((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
        X.smallZariskiTopology).Additive]
    [(Functor.Homotopy.toDerived
        ((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
          X.smallZariskiTopology)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (topology Λ X) AddCommGrpCat.{w})
        (ComplexShape.up ℤ))]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w}),
    IsIsomorphic (DerivedCategory.Q.obj (evalSheafComplex Λ X F))
      ((Homotopy.functor
          ((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
            X.smallZariskiTopology)).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (topology Λ X) AddCommGrpCat.{w}) (0 : ℤ)).obj F)))

#check (AlgebraicGeometry.Scheme.CotangentSite.standardCosimplicial :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : X.smallZariskiSite),
    CosimplicialObject (Functor.Fiber (forgetZariski Λ X) U))

#check (AlgebraicGeometry.Scheme.CotangentSite.standardFunctor :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)],
    X.smallZariskiSite ⥤ CosimplicialObject (category Λ X))

#check (AlgebraicGeometry.Scheme.CotangentSite.evalPresheaf :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (category Λ X)ᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ),
    X.smallZariskiSiteᵒᵖ ⥤ AddCommGrpCat.{w})

#check (AlgebraicGeometry.Scheme.CotangentSite.evalPresheaf_obj :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (category Λ X)ᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) (U : X.smallZariskiSite),
    (evalPresheaf Λ X F n).obj (op U) = F.obj (op (standardAffine Λ X ⦋n⦌ U)))

#check (AlgebraicGeometry.Scheme.CotangentSite.evalComplex :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (category Λ X)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ChainComplex (X.smallZariskiSiteᵒᵖ ⥤ AddCommGrpCat.{w}) ℕ)

#check (AlgebraicGeometry.Scheme.CotangentSite.evalComplex_X :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (category Λ X)ᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ),
    (evalComplex Λ X F).X n = evalPresheaf Λ X F n)

#check (AlgebraicGeometry.Scheme.CotangentSite.evalSheafChain :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{w}] (F : Sheaf (topology Λ X) AddCommGrpCat.{w}),
    ChainComplex (Sheaf X.smallZariskiTopology AddCommGrpCat.{w}) ℕ)

#check (AlgebraicGeometry.Scheme.CotangentSite.evalSheafComplex :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{w}]
    [HasZeroObject (Sheaf X.smallZariskiTopology AddCommGrpCat.{w})] (F : Sheaf (topology Λ X) AddCommGrpCat.{w}),
    CochainComplex (Sheaf X.smallZariskiTopology AddCommGrpCat.{w}) ℤ)

#check (AlgebraicGeometry.Scheme.CotangentSite.evalSheafComplex_X :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{w}]
    [HasZeroObject (Sheaf X.smallZariskiTopology AddCommGrpCat.{w})]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w}) (n : ℕ),
    (evalSheafComplex Λ X F).X (-(n : ℤ)) =
      (presheafToSheaf X.smallZariskiTopology AddCommGrpCat.{w}).obj (evalPresheaf Λ X F.obj n))

#check (AlgebraicGeometry.Scheme.CotangentSite.standardCosimplicial_hasHomSpaces :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (U : X.smallZariskiSite),
    CosimplicialObject.Pointlike.HasHomSpaces (standardCosimplicial Λ X U))

#check (AlgebraicGeometry.Scheme.CotangentSite.evalComplex_homology_isomorphic_fiberHomology_presheaf :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] [UnivLE.{u + 1, w}]
    (F : (category Λ X)ᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ),
    IsIsomorphic ((evalComplex Λ X F).homology n)
      (Bar.presheaf (fiberedOver Λ X) F n))

#check (AlgebraicGeometry.Scheme.CotangentSite.evalComplex_homology_isomorphic_fiberHomology :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] [UnivLE.{u + 1, w}]
    (F : (category Λ X)ᵒᵖ ⥤ AddCommGrpCat.{w}) (U : X.smallZariskiSite) (n : ℕ),
    IsIsomorphic
      (((CosimplicialObject.Evaluation.complex AddCommGrpCat.{w}
        (standardCosimplicialObj Λ X U)).obj F).homology n)
      (Bar.homology (fiberedOver Λ X) F U n))

#check (AlgebraicGeometry.Scheme.CotangentSite.evalSheaf_homology_isomorphic_lowerShriek :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{w}]
    [HasSheafify (topology Λ X) AddCommGrpCat.{w}]
    [((forgetZariski Λ X).sheafPushforwardContinuous AddCommGrpCat.{w}
        (topology Λ X) X.smallZariskiTopology).IsRightAdjoint]
    [HasProjectiveResolutions (Sheaf (topology Λ X) AddCommGrpCat.{w})]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w}) (n : ℕ),
    IsIsomorphic
      ((presheafToSheaf X.smallZariskiTopology AddCommGrpCat.{w}).obj
        ((evalComplex Λ X F.obj).homology n))
      (((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
          X.smallZariskiTopology).leftDerived n |>.obj F))

#check (AlgebraicGeometry.Scheme.CotangentSite.evalSheaf_homology_isomorphic_derivedLowerShriek :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{w}]
    [HasZeroObject (Sheaf X.smallZariskiTopology AddCommGrpCat.{w})]
    [HasSheafify (topology Λ X) AddCommGrpCat.{w}]
    [((forgetZariski Λ X).sheafPushforwardContinuous AddCommGrpCat.{w}
        (topology Λ X) X.smallZariskiTopology).IsRightAdjoint]
    [HasDerivedCategory.{qS} (Sheaf (topology Λ X) AddCommGrpCat.{w})]
    [HasDerivedCategory.{qT} (Sheaf X.smallZariskiTopology AddCommGrpCat.{w})]
    [((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
        X.smallZariskiTopology).Additive]
    [(Functor.Homotopy.toDerived
        ((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
          X.smallZariskiTopology)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (topology Λ X) AddCommGrpCat.{w})
        (ComplexShape.up ℤ))]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w}) (n : ℕ),
    IsIsomorphic
      ((presheafToSheaf X.smallZariskiTopology AddCommGrpCat.{w}).obj
        ((evalComplex Λ X F.obj).homology n))
      ((DerivedCategory.homologyFunctor
          (Sheaf X.smallZariskiTopology AddCommGrpCat.{w}) (-(n : ℤ))).obj
        ((Homotopy.functor
          ((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
            X.smallZariskiTopology)).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (topology Λ X) AddCommGrpCat.{w}) (0 : ℤ)).obj F))))

end AlgebraicGeometry.Scheme.CotangentSite
