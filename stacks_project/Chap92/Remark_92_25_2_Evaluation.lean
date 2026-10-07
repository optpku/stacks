module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap92.Remark_92_25_2_Cosimplicial

/-!
# Evaluation of abelian sheaves on standard fibrewise affine spaces

The rule `U ↦ F(A_{n,U})` is a presheaf on `X_Zar`.  Sheafifying in each cohomological
degree `-n` produces a complex of abelian sheaves computing `Lπ_!(F)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits
open AlgebraicTopology HomologicalComplex
open scoped AlgebraicGeometry Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

/-- The presheaf `U ↦ F(A_{n,U})` on the small Zariski site of `X`. -/
def evalPresheaf (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (Obj Λ X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    X.smallZariskiSiteᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj U := F.obj (op (standardAffine Λ X ⦋n⦌ U.unop))
  map {U V} f := F.map (standardAffineRestrict Λ X f.unop ⦋n⦌).op
  map_id := sorry
  map_comp := sorry

/-- Evaluating `evalPresheaf F n` at `U` recovers `F(A_{n,U})`. -/
theorem evalPresheaf_obj (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (Obj Λ X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) (U : X.smallZariskiSite) :
    (evalPresheaf Λ X F n).obj (op U) = F.obj (op (standardAffine Λ X ⦋n⦌ U)) :=
  sorry

/-- The simplicial abelian group `F(A_{•,U})`. -/
def evalSimplicial (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (Obj Λ X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (U : X.smallZariskiSite) :
    SimplicialObject AddCommGrpCat.{u + 1} :=
  (CosimplicialObject.Evaluation.simplicial AddCommGrpCat.{u + 1}
      (standardCosimplicialObj Λ X U)).obj F

/-- Evaluation of an abelian sheaf `F` on `A_{•,U}`, as a chain complex. -/
def evalChain (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (U : X.smallZariskiSite) :
    ChainComplex AddCommGrpCat.{u + 1} ℕ :=
  (alternatingFaceMapComplex AddCommGrpCat.{u + 1}).obj
    (evalSimplicial Λ X F.obj U)

/-- The degree-`n` term of `evalChain F U` is `F(A_{n,U})`. -/
theorem evalChain_X (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1})
    (U : X.smallZariskiSite) (n : ℕ) :
    (evalChain Λ X F U).X n = F.obj.obj (op (standardAffine Λ X ⦋n⦌ U)) :=
  sorry

/-- Restriction of `F(A_{•,U})` along `V ⟶ U`. -/
def evalSimplicialMap (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (Obj Λ X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) {V U : X.smallZariskiSite} (f : V ⟶ U) :
    evalSimplicial Λ X F U ⟶ evalSimplicial Λ X F V where
  app n := F.map (standardAffineRestrict Λ X f n.unop).op
  naturality := fun {_ _} _ ↦ sorry

/-- The complex of presheaves `U ↦ F(A_{•,U})` on `X_Zar`. -/
def evalComplex (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (Obj Λ X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    ChainComplex (X.smallZariskiSiteᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ where
  X n :=
    { obj U :=
        ((alternatingFaceMapComplex AddCommGrpCat.{u + 1}).obj
          (evalSimplicial Λ X F U.unop)).X n
      map {U V} f :=
        ((alternatingFaceMapComplex AddCommGrpCat.{u + 1}).map
          (evalSimplicialMap Λ X F f.unop)).f n
      map_id := sorry
      map_comp := sorry }
  d i j :=
    { app U :=
        ((alternatingFaceMapComplex AddCommGrpCat.{u + 1}).obj
          (evalSimplicial Λ X F U.unop)).d i j
      naturality := fun {_ _} _ ↦ sorry }
  shape := sorry
  d_comp_d' := sorry

/-- The degree-`n` term of `evalComplex F` agrees with `evalPresheaf F n`. -/
theorem evalComplex_X (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (Obj Λ X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (evalComplex Λ X F).X n = evalPresheaf Λ X F n :=
  sorry

/-- Degreewise sheafification of `U ↦ F(A_{•,U})`, as a chain complex of abelian sheaves. -/
def evalSheafChain (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasWeakSheafify X.smallZariskiTopology AddCommGrpCat.{u + 1}]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) :
    ChainComplex (Sheaf X.smallZariskiTopology AddCommGrpCat.{u + 1}) ℕ :=
  ((presheafToSheaf X.smallZariskiTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
    (evalComplex Λ X F.obj)

/-- The complex of abelian sheaves on `X_Zar` whose term in cohomological degree `-n`
is the sheafification of `U ↦ F(A_{n,U})`. -/
def evalSheafComplex (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasWeakSheafify X.smallZariskiTopology AddCommGrpCat.{u + 1}]
    [HasZeroObject (Sheaf X.smallZariskiTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) :
    CochainComplex (Sheaf X.smallZariskiTopology AddCommGrpCat.{u + 1}) ℤ :=
  (evalSheafChain Λ X F).extend ComplexShape.embeddingDownNat

/-- In cohomological degree `-n`, `evalSheafComplex F` is the sheafification of
`U ↦ F(A_{n,U})`. -/
theorem evalSheafComplex_X (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasWeakSheafify X.smallZariskiTopology AddCommGrpCat.{u + 1}]
    [HasZeroObject (Sheaf X.smallZariskiTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (evalSheafComplex Λ X F).X (-n) =
      (presheafToSheaf X.smallZariskiTopology AddCommGrpCat.{u + 1}).obj
        (evalPresheaf Λ X F.obj n) :=
  sorry

end AlgebraicGeometry.Scheme.CotangentSite
