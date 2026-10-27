/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.StandardResolution
public import ReasLib.CategoryTheory.Sites.CosimplicialEvaluation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.Evaluation
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

/-!
# Standard affine resolutions and `Lπ_!` on algebraic spaces

Remark 92.27.2 records the functorial standard affine object `A_{•,U}` in the fibre of
`C_{X/Λ}` over an étale `U`, the pointlike mapping-space hypothesis of Lemma 21.39.7, and
the computation of `Lπ_!(F)` by evaluating an abelian sheaf `F` on `A_{•,U}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open scoped Simplicial

noncomputable section

universe u w q

variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))

/- Remark 92.27.2 (1): for `U` in `X_étale`, the standard polynomial resolution of `𝒪_X(U)`
over `Λ` yields the functorial cosimplicial object `A_{•,U}` of the fibre of `C_{X/Λ}` over
`U`, with `A_{n,U} = Spec(P_{n,U})`. -/
@[stacks 08VL]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.standardAffine Λ X :
  smallEtaleSite X ⥤ CosimplicialObject (category Λ X))

/- Remark 92.27.2: the affine target in each degree is the spectrum of the actual
standard-resolution term. -/
@[stacks 08VL]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.standardAffineSpecIso Λ X :
  ∀ (U : smallEtaleSite X) (n : SimplexCategory),
    (affineScheme Λ X).obj (((standardAffine Λ X).obj U).obj n) ≅
      Spec (standardTerm Λ U n).right)

/- Remark 92.27.2: the cosimplicial object is over the constant chart and hence lies in
the actual projection fiber. -/
@[stacks 08VL]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.standardAffine_comp_forget Λ X :
  ∀ U : smallEtaleSite X,
    (standardAffine Λ X).obj U ⋙ forget Λ X = (Functor.const _).obj U)

/- Remark 92.27.2 (2): `A_{•,U}` is a cosimplicial object of the fibre as in Cohomology on
Sites, Lemma 21.39.7. -/
@[stacks 08VL]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.standardAffine_hasHomSpaces Λ X :
  ∀ U : smallEtaleSite X, CosimplicialObject.Pointlike.HasHomSpaces
    (Functor.Fiber.inducedFunctor (standardAffine_comp_forget Λ X U)))

variable [UnivLE.{u + 1, w}]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{w}]
variable [HasSheafify (topology Λ X) AddCommGrpCat.{w}]
variable [((forget Λ X).sheafPushforwardContinuous AddCommGrpCat.{w}
  (topology Λ X) (smallEtaleTopology X)).IsRightAdjoint]
variable (F : Sheaf (topology Λ X) AddCommGrpCat.{w})

/- Remark 92.27.2: evaluation defines the complex of presheaves on the étale site. -/
@[stacks 08VL]
#check (CategoryTheory.CosimplicialObject.Evaluation.Family.presheafComplex
  (standardAffine Λ X) F.obj : ChainComplex ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{w}) ℕ)

/- Remark 92.27.2 (3): for an abelian sheaf `F` on `C_{X/Λ}`, the cohomology of the
presheaf complex `U ↦ F(A_{•,U})` computes the homology of `F` on the fibre category. -/
@[stacks 08VL]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.eval_homology_iso Λ X F :
  ∀ (U : smallEtaleSite X) (n : ℕ), IsIsomorphic
    (((CosimplicialObject.Evaluation.complex AddCommGrpCat.{w}
      ((standardAffine Λ X).obj U)).obj F.obj).homology n)
    (FiberedCategoryOver.FiberHomology.Bar.homology
      (FiberedCategoryOver.ofFunctor (forget Λ X)) F.obj U n))

section Projective
variable [HasProjectiveResolutions (Sheaf (topology Λ X) AddCommGrpCat.{w})]

/- Remark 92.27.2 (4): sheafification of that homology computes `L_n π_!(F)`, by Cohomology
on Sites, Lemma 21.40.2. -/
@[stacks 08VL]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.sheafify_iso_lowerShriek Λ X F :
  ∀ n : ℕ, IsIsomorphic
    ((presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{w}).obj
      ((CosimplicialObject.Evaluation.Family.presheafComplex
        (standardAffine Λ X) F.obj).homology n))
    ((((forget Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
      (smallEtaleTopology X)).leftDerived n).obj F))
end Projective

/- Remark 92.27.2: the term in cochain degree `-n` is the associated sheaf of
degree-`n` evaluation. -/
@[stacks 08VL]
#check (CategoryTheory.CosimplicialObject.Evaluation.Family.sheafComplex_X_neg
  (standardAffine Λ X) F.obj (smallEtaleTopology X) :
  ∀ n : ℕ,
    (CosimplicialObject.Evaluation.Family.sheafComplex
      (standardAffine Λ X) F.obj (smallEtaleTopology X)).X (-(n : ℤ)) =
    (presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{w}).obj
      ((CosimplicialObject.Evaluation.Family.presheafComplex
        (standardAffine Λ X) F.obj).X n))

variable [HasDerivedCategory.{q} (Sheaf (topology Λ X) AddCommGrpCat.{w})]
variable [HasDerivedCategory.{q} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w})]
variable [((forget Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
    (smallEtaleTopology X)).Additive]
variable [(Functor.Homotopy.toDerived
    ((forget Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
      (smallEtaleTopology X))).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf (topology Λ X) AddCommGrpCat.{w})
    (ComplexShape.up ℤ))]

/- Remark 92.27.2 (5): equivalently, the complex of sheaves whose term in degree `-n` is the
sheafification of `U ↦ F(A_{n,U})` computes `Lπ_!(F)`. -/
@[stacks 08VL]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.evalSheafComplex_iso Λ X F :
  IsIsomorphic
    (DerivedCategory.Q.obj (CosimplicialObject.Evaluation.Family.sheafComplex
      (standardAffine Λ X) F.obj (smallEtaleTopology X)))
    ((Functor.LeftDerived.Homotopy.functor
      ((forget Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
        (smallEtaleTopology X))).obj
      ((DerivedCategory.singleFunctor
        (Sheaf (topology Λ X) AddCommGrpCat.{w}) (0 : ℤ)).obj F)))

/- Remark 92.27.2: without projective resolutions, sheafified degree-`n` homology is
degree-`-n` homology of total left-derived projection lower shriek. -/
@[stacks 08VL]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.evalSheafComplex_homology_iso Λ X F :
  ∀ n : ℕ, IsIsomorphic
    ((presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{w}).obj
      ((CosimplicialObject.Evaluation.Family.presheafComplex
        (standardAffine Λ X) F.obj).homology n))
    ((DerivedCategory.homologyFunctor
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w}) (-(n : ℤ))).obj
      ((Functor.LeftDerived.Homotopy.functor
        ((forget Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
          (smallEtaleTopology X))).obj
        ((DerivedCategory.singleFunctor
          (Sheaf (topology Λ X) AddCommGrpCat.{w}) (0 : ℤ)).obj F))))
