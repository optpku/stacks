module

public import stacks_project.Chap92.Remark_92_25_2_Cosimplicial
public import stacks_project.Chap92.Remark_92_25_2_Evaluation
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.Fibered.CategoryHomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computing `Lπ_!` by the standard fibrewise polynomial resolution

Remark 92.25.2 records that `A_{•,U} = Spec(P_{•,U})` is a pointlike cosimplicial object
of the fibre of `C_{X/Λ}` over `U`, that `U ↦ F(A_{•,U})` computes fibre homology, and
that sheafification computes `Lπ_!(F)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits AlgebraicTopology
open HomologicalComplex FiberedCategoryOver.FiberHomology Functor.LeftDerived
open scoped AlgebraicGeometry Simplicial

noncomputable section

universe u q

namespace AlgebraicGeometry.Scheme.CotangentSite

/-- Remark 92.25.2 (1): `A_{•,U}` is a cosimplicial object of the fibre category
`C_{O_X(U)/Λ}` of `C_{X/Λ}` over `U` as in Lemma 21.39.7. -/
@[stacks 08VB]
theorem standardCosimplicial_hasHomSpaces (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (U : X.smallZariskiSite) :
    CosimplicialObject.Pointlike.HasHomSpaces (standardCosimplicial Λ X U) :=
  sorry

/-- Remark 92.25.2 (2): for an abelian sheaf `F` on `C_{X/Λ}`, the complex of
presheaves `U ↦ F(A_{•,U})` computes the homology of `F` on the fibre category. -/
@[stacks 08VB]
theorem evalComplex_homology_isomorphic_fiberHomology
    (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1})
    (U : X.smallZariskiSite) (n : ℕ) :
    IsIsomorphic ((evalChain Λ X F U).homology n)
      (Bar.homology (fiberedOver Λ X) F.obj U n) :=
  sorry

/-- Remark 92.25.2 (3): sheafification of `U ↦ F(A_{•,U})` computes
`L_n π_!(F)` on `X_Zar`. -/
@[stacks 08VB]
theorem evalSheaf_homology_isomorphic_lowerShriek
    (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology Λ X) AddCommGrpCat.{u + 1}]
    [((forgetZariski Λ X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (topology Λ X) X.smallZariskiTopology).IsRightAdjoint]
    [HasProjectiveResolutions (Sheaf (topology Λ X) AddCommGrpCat.{u + 1})]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic
      ((presheafToSheaf X.smallZariskiTopology AddCommGrpCat.{u + 1}).obj
        ((evalComplex Λ X F.obj).homology n))
      (((forgetZariski Λ X).sheafPullback AddCommGrpCat.{u + 1} (topology Λ X)
          X.smallZariskiTopology).leftDerived n |>.obj F) :=
  sorry

/-- Remark 92.25.2 (4): the complex of sheaves whose term in degree `-n` is the
sheafification of `U ↦ F(A_{n,U})` computes `Lπ_!(F)`. -/
@[stacks 08VB]
theorem evalSheafComplex_computes
    (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u + 1}]
    [HasWeakSheafify X.smallZariskiTopology AddCommGrpCat.{u + 1}]
    [HasZeroObject (Sheaf X.smallZariskiTopology AddCommGrpCat.{u + 1})]
    [HasSheafify (topology Λ X) AddCommGrpCat.{u + 1}]
    [((forgetZariski Λ X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (topology Λ X) X.smallZariskiTopology).IsRightAdjoint]
    [HasDerivedCategory.{q} (Sheaf (topology Λ X) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{q} (Sheaf X.smallZariskiTopology AddCommGrpCat.{u + 1})]
    [((forgetZariski Λ X).sheafPullback AddCommGrpCat.{u + 1} (topology Λ X)
        X.smallZariskiTopology).Additive]
    [(Functor.Homotopy.toDerived
        ((forgetZariski Λ X).sheafPullback AddCommGrpCat.{u + 1} (topology Λ X)
          X.smallZariskiTopology)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (topology Λ X) AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ))]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) :
    IsIsomorphic (DerivedCategory.Q.obj (evalSheafComplex Λ X F))
      ((Homotopy.functor
          ((forgetZariski Λ X).sheafPullback AddCommGrpCat.{u + 1} (topology Λ X)
            X.smallZariskiTopology)).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)) :=
  sorry

end AlgebraicGeometry.Scheme.CotangentSite
