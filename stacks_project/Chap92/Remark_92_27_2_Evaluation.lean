/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.Fibered.CategoryHomology
public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar.LeftDerived
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import stacks_project.Chap92.«92_27_1_1_Morphism»
public import stacks_project.Chap92.Remark_92_27_2_Affine

/-!
# Evaluation of sheaves on standard affine objects

This leaf owns the complex of presheaves `U ↦ F(A_{•,U})`, its degreewise sheafification as a
complex of sheaves in cochain degree `-n`, and the comparisons with fibre homology and
`Lπ_!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry Simplicial

noncomputable section

universe u q

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))

/-- The fibred category `C_{X/Λ}` over the small étale site of `X`. -/
abbrev fibered : FiberedCategoryOver (smallEtaleSite X) :=
  FiberedCategoryOver.ofFunctor (forget Λ X)

/-- The projection of `fibered Λ X` is `forget Λ X`. -/
theorem fibered_p : (fibered Λ X).p = forget Λ X :=
  sorry

/-- Evaluation of `F` on the standard affine cosimplicial object over `U`. -/
def evalChain (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (U : smallEtaleSite X) :
    ChainComplex AddCommGrpCat.{u + 1} ℕ :=
  (CosimplicialObject.Evaluation.complex AddCommGrpCat.{u + 1}
    ((standardAffine Λ X).obj U)).obj F.obj

/-- The chain map `F(A_{•,U}) ⟶ F(A_{•,V})` induced by `g : V ⟶ U`. -/
def evalChainMap (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1})
    {U V : smallEtaleSite X} (g : V ⟶ U) :
    evalChain Λ X F U ⟶ evalChain Λ X F V where
  f n := F.obj.map (op (((standardAffine Λ X).map g).app ⦋n⦌))
  comm' := sorry

/-- Unfolding of the components of `evalChainMap`. -/
theorem evalChainMap_f (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1})
    {U V : smallEtaleSite X} (g : V ⟶ U) (n : ℕ) :
    (evalChainMap Λ X F g).f n =
      F.obj.map (op (((standardAffine Λ X).map g).app ⦋n⦌)) :=
  sorry

/-- The degree-`n` presheaf `U ↦ F(A_{n,U})` on the small étale site of `X`. -/
def evalPresheafDegree (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj U := (evalChain Λ X F U.unop).X n
  map f := (evalChainMap Λ X F f.unop).f n
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The complex of abelian presheaves `U ↦ F(A_{•,U})`. -/
def evalPresheaf (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) :
    ChainComplex ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ where
  X n := evalPresheafDegree Λ X F n
  d i j :=
    { app U := (evalChain Λ X F U.unop).d i j
      naturality := fun _ _ _ ↦ sorry }
  shape := sorry
  d_comp_d' := sorry

/-- Unfolding of `evalPresheaf` in each chain degree. -/
theorem evalPresheaf_X (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (n : ℕ)
    (U : (smallEtaleSite X)ᵒᵖ) :
    ((evalPresheaf Λ X F).X n).obj U = (evalChain Λ X F U.unop).X n :=
  sorry

variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]

/-- Degreewise sheafification of `U ↦ F(A_{•,U})`, as a chain complex of abelian sheaves. -/
def evalSheafChain (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) :
    ChainComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ℕ :=
  ((presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (evalPresheaf Λ X F)

/-- The complex of sheaves whose term in cochain degree `-n` is the sheafification of
`U ↦ F(A_{n,U})`. -/
def evalSheafComplex (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) :
    CochainComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ℤ :=
  (ComplexShape.embeddingDownNat.extendFunctor
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})).obj
    (evalSheafChain Λ X F)

/-- Unfolding of `evalSheafChain` in each chain degree. -/
theorem evalSheafChain_X (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (evalSheafChain Λ X F).X n =
      (presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        ((evalPresheaf Λ X F).X n) :=
  sorry

/-- The sheaf in cochain degree `-n` of `evalSheafComplex` is the sheafification of
`U ↦ F(A_{n,U})`. -/
theorem evalSheafComplex_X_neg (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (evalSheafComplex Λ X F).X (-n : ℤ) =
      (presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        ((evalPresheaf Λ X F).X n) :=
  sorry

variable [HasSheafify (topology Λ X) AddCommGrpCat.{u + 1}]
variable [((forget Λ X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology Λ X) (smallEtaleTopology X)).IsRightAdjoint]

/-- Cohomology of `U ↦ F(A_{•,U})` computes the homology of `F` on the fibre over `U`. -/
theorem eval_homology_iso (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (n : ℕ) :
    IsIsomorphic ((evalChain Λ X F U).homology n)
      (FiberedCategoryOver.FiberHomology.Bar.homology (fibered Λ X) F.obj U n) :=
  sorry

/-- Sheafification of the homology of `U ↦ F(A_{•,U})` computes `L_n π_!(F)`. -/
theorem sheafify_iso_lowerShriek
    [HasProjectiveResolutions (Sheaf (topology Λ X) AddCommGrpCat.{u + 1})]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic
      ((presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        ((evalPresheaf Λ X F).homology n))
      (((forget Λ X).sheafPullback AddCommGrpCat.{u + 1} (topology Λ X)
          (smallEtaleTopology X)).leftDerived n |>.obj F) :=
  sorry

variable [HasDerivedCategory.{q} (Sheaf (topology Λ X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{q} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [((forget Λ X).sheafPullback AddCommGrpCat.{u + 1} (topology Λ X)
    (smallEtaleTopology X)).Additive]
variable [(Functor.Homotopy.toDerived
    ((forget Λ X).sheafPullback AddCommGrpCat.{u + 1} (topology Λ X)
      (smallEtaleTopology X))).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf (topology Λ X) AddCommGrpCat.{u + 1})
    (ComplexShape.up ℤ))]

/-- The complex of sheaves with term in degree `-n` the sheafification of `U ↦ F(A_{n,U})`
computes `Lπ_!(F)`. -/
theorem evalSheafComplex_iso (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) :
    IsIsomorphic (DerivedCategory.Q.obj (evalSheafComplex Λ X F))
      ((Functor.LeftDerived.Homotopy.functor
          ((forget Λ X).sheafPullback AddCommGrpCat.{u + 1} (topology Λ X)
            (smallEtaleTopology X))).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
