/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap58.Theorem_58_6_2_InducedHom
public import stacks_project.Chap59.Lemma_59_65_1_Equivalence
public import stacks_project.Chap59.Lemma_59_65_2_Equivalence

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Action.ModuleCat
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.Scheme

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

/-- Inverse image along `f` sends finite locally constant étale sheaves of sets to
finite locally constant étale sheaves of sets. -/
theorem sheafPullback_isFiniteLocallyConstant
    [HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : Sheaf.IsFiniteLocallyConstant F) :
    Sheaf.IsFiniteLocallyConstant
      ((smallEtalePullback f).sheafPullback (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology |>.obj F) :=
  sorry

/-- Inverse image of finite locally constant étale sheaves of sets along `f : Y ⟶ X`. -/
noncomputable def finiteLocallyConstantPullback
    [HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension P] :
    (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory ⥤
      (Sheaf.finiteLocallyConstant Y.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstant Y.smallEtaleTopology).lift
    ((Sheaf.finiteLocallyConstant X.smallEtaleTopology).ι ⋙
      (smallEtalePullback f).sheafPullback (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology)
    fun F ↦ sheafPullback_isFiniteLocallyConstant f F.obj F.property

/-- The set-level inverse-image functor is sheaf pullback on the underlying sheaf. -/
theorem finiteLocallyConstantPullback_obj
    [HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory) :
    ((finiteLocallyConstantPullback f).obj F).obj =
      ((smallEtalePullback f).sheafPullback (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology).obj F.obj :=
  sorry

/-- Inverse image along `f` sends finite locally constant étale sheaves of abelian groups
to finite locally constant étale sheaves of abelian groups. -/
theorem sheafPullback_isFiniteLocallyConstantAddCommGrp
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Sheaf.IsFiniteLocallyConstantAddCommGrp F) :
    Sheaf.IsFiniteLocallyConstantAddCommGrp
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology |>.obj F) :=
  sorry

/-- Inverse image of finite locally constant étale sheaves of abelian groups along `f`. -/
noncomputable def finiteLocallyConstantAddCommGrpPullback
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory ⥤
      (Sheaf.finiteLocallyConstantAddCommGrp Y.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstantAddCommGrp Y.smallEtaleTopology).lift
    ((Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).ι ⋙
      (smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology)
    fun F ↦ sheafPullback_isFiniteLocallyConstantAddCommGrp f F.obj F.property

/-- The abelian inverse-image functor is sheaf pullback on the underlying sheaf. -/
theorem finiteLocallyConstantAddCommGrpPullback_obj
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    ((finiteLocallyConstantAddCommGrpPullback f).obj F).obj =
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology).obj F.obj :=
  sorry

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Inverse image along `f` sends finite-type locally constant étale sheaves of `Λ`-modules
to finite-type locally constant étale sheaves of `Λ`-modules. -/
theorem sheafPullback_isFiniteTypeLocallyConstantModule
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Sheaf.IsFiniteTypeLocallyConstantModule F) :
    Sheaf.IsFiniteTypeLocallyConstantModule
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology |>.obj F) :=
  sorry

/-- Inverse image of finite-type locally constant étale sheaves of `Λ`-modules along `f`. -/
noncomputable def finiteTypeLocallyConstantModulePullback
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
      (Sheaf.finiteTypeLocallyConstantModule Y.smallEtaleTopology Λ).FullSubcategory :=
  (Sheaf.finiteTypeLocallyConstantModule Y.smallEtaleTopology Λ).lift
    ((Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).ι ⋙
      (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology)
    fun F ↦ sheafPullback_isFiniteTypeLocallyConstantModule f Λ F.obj F.property

/-- The module-valued inverse-image functor is sheaf pullback on the underlying sheaf. -/
theorem finiteTypeLocallyConstantModulePullback_obj
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    ((finiteTypeLocallyConstantModulePullback f Λ).obj F).obj =
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology).obj F.obj :=
  sorry

/-- Restriction of discrete modules along a continuous group homomorphism preserves the
open-stabilizer property. -/
theorem openStabilizer_res {R : Type v} [Ring R]
    {G H : Type u} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (φ : G →ₜ* H) (M : Action (ModuleCat.{max v u} R) H)
    (hM : openStabilizer R H M) :
    openStabilizer R G ((Action.res (ModuleCat.{max v u} R) φ.toMonoidHom).obj M) :=
  sorry

/-- Restriction of discrete continuous modules along a continuous group homomorphism. -/
noncomputable def discreteModuleRes {R : Type v} [Ring R]
    {G H : Type u} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (φ : G →ₜ* H) :
    DiscreteModuleCat R H ⥤ DiscreteModuleCat R G :=
  (openStabilizer R G).lift
    ((openStabilizer R H).ι ⋙ Action.res (ModuleCat.{max v u} R) φ.toMonoidHom)
    fun M ↦ openStabilizer_res φ M.obj M.property

/-- Restriction of finite discrete `ℤ`-modules along `etaleFundamentalGroupMap f ybar`. -/
theorem finiteDiscreteModule_res
    [ConnectedSpace Y] [ConnectedSpace X] (ybar : GeometricPoint Y)
    (M : DiscreteModuleCat ℤ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp ybar f))))
    (hM : IsFiniteDiscreteModule ℤ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp ybar f)))
      M) :
    IsFiniteDiscreteModule ℤ (Aut (standardFiniteEtaleFiber ybar))
      ((discreteModuleRes (etaleFundamentalGroupMap f ybar)).obj M) :=
  sorry

/-- Restriction of finite discrete `π₁`-modules along the continuous homomorphism induced by `f`. -/
noncomputable def etaleFundamentalGroupMap_resFiniteDiscreteModule
    [ConnectedSpace Y] [ConnectedSpace X] (ybar : GeometricPoint Y) :
    (finiteDiscreteModule ℤ
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp ybar f)))).FullSubcategory ⥤
      (finiteDiscreteModule ℤ (Aut (standardFiniteEtaleFiber ybar))).FullSubcategory :=
  (finiteDiscreteModule ℤ (Aut (standardFiniteEtaleFiber ybar))).lift
    ((finiteDiscreteModule ℤ
        (Aut (standardFiniteEtaleFiber (geometricPointPostcomp ybar f)))).ι ⋙
      discreteModuleRes (etaleFundamentalGroupMap f ybar))
    fun M ↦ finiteDiscreteModule_res f ybar M.obj M.property

/-- Restriction of finite-type discrete `Λ`-modules along `etaleFundamentalGroupMap f ybar`. -/
theorem finiteTypeDiscreteModule_res
    [ConnectedSpace Y] [ConnectedSpace X] (ybar : GeometricPoint Y)
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp ybar f))))
    (hM : IsFiniteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp ybar f))) M) :
    IsFiniteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber ybar))
      ((discreteModuleRes (etaleFundamentalGroupMap f ybar)).obj M) :=
  sorry

/-- Restriction of finite-type discrete `π₁`-modules along the continuous homomorphism
induced by `f`. -/
noncomputable def etaleFundamentalGroupMap_resFiniteTypeDiscreteModule
    [ConnectedSpace Y] [ConnectedSpace X] (ybar : GeometricPoint Y) :
    (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp ybar f)))).FullSubcategory ⥤
      (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber ybar))).FullSubcategory :=
  (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber ybar))).lift
    ((finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (geometricPointPostcomp ybar f)))).ι ⋙
      discreteModuleRes (etaleFundamentalGroupMap f ybar))
    fun M ↦ finiteTypeDiscreteModule_res f Λ ybar M.obj M.property

/-- Remark 59.65.3 (1): the equivalence of Lemma 59.65.1 (1) between finite locally constant
étale sheaves of sets and finite `π₁`-sets is compatible with inverse image along a morphism
`f : Y ⟶ X` of connected schemes. The right vertical functor is restriction of finite
`π₁(X, f(ȳ))`-sets along the continuous homomorphism `π₁(Y, ȳ) → π₁(X, f(ȳ))` induced by `f`. -/
@[stacks 0DV6]
theorem finiteLocallyConstant_pullback_catCommSq
    [ConnectedSpace Y] [ConnectedSpace X]
    [HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y) :
    Nonempty
      (CatCommSq (finiteLocallyConstantPullback f)
        (finiteLocallyConstant_equivalence_finitePi1Sets
          (geometricPointPostcomp ybar f)).functor
        (finiteLocallyConstant_equivalence_finitePi1Sets ybar).functor
        (etaleFundamentalGroupMap_res f ybar)) :=
  sorry

/-- Remark 59.65.3 (2): the same 2-commutativity for finite locally constant étale sheaves of
abelian groups, with restriction of finite discrete `π₁`-modules along
`etaleFundamentalGroupMap f ybar`. -/
@[stacks 0DV6]
theorem finiteLocallyConstantAddCommGrp_pullback_catCommSq
    [ConnectedSpace Y] [ConnectedSpace X]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y) :
    Nonempty
      (CatCommSq (finiteLocallyConstantAddCommGrpPullback f)
        (finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules
          (geometricPointPostcomp ybar f)).functor
        (finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules ybar).functor
        (etaleFundamentalGroupMap_resFiniteDiscreteModule f ybar)) :=
  sorry

/-- Remark 59.65.3 (3): the same 2-commutativity for finite-type locally constant étale sheaves
of modules over a finite ring `Λ`. -/
@[stacks 0DV6]
theorem finiteTypeLocallyConstantModule_pullback_lambda_catCommSq
    [Finite Λ]
    [ConnectedSpace Y] [ConnectedSpace X]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y) :
    Nonempty
      (CatCommSq (finiteTypeLocallyConstantModulePullback f Λ)
        (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
          (geometricPointPostcomp ybar f)).functor
        (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ ybar).functor
        (etaleFundamentalGroupMap_resFiniteTypeDiscreteModule f Λ ybar)) :=
  sorry

/-- Remark 59.65.3 (4): the same 2-commutativity for Lemma 59.65.2, with `Λ` an arbitrary ring
and both schemes irreducible and geometrically unibranch. -/
@[stacks 0DV6]
theorem finiteTypeLocallyConstantModule_pullback_catCommSq
    [ConnectedSpace Y] [ConnectedSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace X]
    (huniY : Y.isGeometricallyUnibranch) (huniX : X.isGeometricallyUnibranch)
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y) :
    Nonempty
      (CatCommSq (finiteTypeLocallyConstantModulePullback f Λ)
        (finiteTypeLocallyConstantModule_equivalence_finitePi1Modules Λ huniX
          (geometricPointPostcomp ybar f)).functor
        (finiteTypeLocallyConstantModule_equivalence_finitePi1Modules Λ huniY ybar).functor
        (etaleFundamentalGroupMap_resFiniteTypeDiscreteModule f Λ ybar)) :=
  sorry

end AlgebraicGeometry.Scheme
