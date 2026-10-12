/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import stacks_project.Chap85.Lemma_85_3_5_Stage

/-!
# Componentwise coproduct formula for stage lower shriek

Restriction of `g^{Sh}_{n!} G` (resp. `g_{n!} G`) to the degree-`m` site is the
coproduct (resp. direct sum) of the inverse images `f_φ⁻¹ G` over simplex operators
`φ : n ⟶ m`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]

/-- The natural transformation `(C.map φ) ⋙ ofStage m ⟶ ofStage n` whose component at `U`
is the total-category morphism `(φ, 𝟙 (u_φ U))`. -/
def stageInclusionWhisker {n m : SimplexCategory} (φ : n ⟶ m) :
    (C.map φ).toFunctor ⋙ ofStage C m ⟶ ofStage C n where
  app U := homMk φ (𝟙 ((C.map φ).toFunctor.obj U))
  naturality := sorry

/-- The component of `stageInclusionWhisker` at a stage object is `homMk φ (𝟙 _)`. -/
theorem stageInclusionWhisker_app {n m : SimplexCategory} (φ : n ⟶ m) (U : C.obj n) :
    (stageInclusionWhisker C φ).app U =
      (homMk φ (𝟙 ((C.map φ).toFunctor.obj U)) :
        ((C.map φ).toFunctor ⋙ ofStage C m).obj U ⟶ (ofStage C n).obj U) :=
  sorry

/-- The composite `u_φ ⋙ ofStage m` is continuous for the stage and total topologies. -/
instance ofStage_comp_isContinuous {n m : SimplexCategory} (φ : n ⟶ m) :
    ((C.map φ).toFunctor ⋙ ofStage C m).IsContinuous
      (J n).toGrothendieck (topology C J) :=
  Functor.isContinuous_comp (C.map φ).toFunctor (ofStage C m)
    (J n).toGrothendieck (J m).toGrothendieck (topology C J)

/-- Inverse image `f_φ⁻¹` of type-valued sheaves along a simplex operator `φ : n ⟶ m`. -/
abbrev stageFacePullback {n m : SimplexCategory} (φ : n ⟶ m) :
    Sheaf ((J n).toGrothendieck) (Type w) ⥤ Sheaf ((J m).toGrothendieck) (Type w) :=
  (C.map φ).toFunctor.sheafPullback (Type w) (J n).toGrothendieck (J m).toGrothendieck

/-- `stageFacePullback φ` is sheaf pullback along `u_φ`. -/
theorem stageFacePullback_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    stageFacePullback C J φ =
      (C.map φ).toFunctor.sheafPullback (Type w) (J n).toGrothendieck (J m).toGrothendieck :=
  sorry

/-- The canonical component map `f_φ⁻¹ G ⟶ (g^{Sh}_{n!} G)_m`. -/
def sheafLowerShriek_component {n m : SimplexCategory} (φ : n ⟶ m)
    (G : Sheaf ((J n).toGrothendieck) (Type w)) :
    ((C.map φ).toFunctor.sheafPullback (Type w)
      (J n).toGrothendieck (J m).toGrothendieck).obj G ⟶
      (stageRestrict C J (Type w) m).obj ((sheafLowerShriek C J n).obj G) :=
  (((C.map φ).toFunctor.sheafAdjunctionContinuous (Type w)
      (J n).toGrothendieck (J m).toGrothendieck).homEquiv
    G ((stageRestrict C J (Type w) m).obj ((sheafLowerShriek C J n).obj G))).symm
  ((sheafLowerShriek_adjunction C J n).unit.app G ≫
    (sheafPushforwardContinuousNatTrans (stageInclusionWhisker C φ) (Type w)
        (J n).toGrothendieck (topology C J)).app ((sheafLowerShriek C J n).obj G) ≫
    (sheafPushforwardContinuousComp (C.map φ).toFunctor (ofStage C m) (Type w)
        (J n).toGrothendieck (J m).toGrothendieck (topology C J)).inv.app
      ((sheafLowerShriek C J n).obj G))

/-- The coproduct comparison morphism
`∐_{φ : n ⟶ m} f_φ⁻¹ G ⟶ (g^{Sh}_{n!} G)_m`. -/
def sheafLowerShriek_componentCoproductHom (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m)) (Sheaf ((J m).toGrothendieck) (Type w))]
    (G : Sheaf ((J n).toGrothendieck) (Type w)) :
    (∐ fun φ : n ⟶ m =>
      ((C.map φ).toFunctor.sheafPullback (Type w)
        (J n).toGrothendieck (J m).toGrothendieck).obj G) ⟶
      (stageRestrict C J (Type w) m).obj ((sheafLowerShriek C J n).obj G) :=
  Sigma.desc fun φ => sheafLowerShriek_component C J φ G

/-- The coproduct comparison is the coproduct of the component maps. -/
theorem sheafLowerShriek_componentCoproductHom_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m)) (Sheaf ((J m).toGrothendieck) (Type w))]
    (G : Sheaf ((J n).toGrothendieck) (Type w)) :
    sheafLowerShriek_componentCoproductHom C J n m G =
      Sigma.desc fun φ => sheafLowerShriek_component C J φ G :=
  sorry

/-- The coproduct comparison morphism is an isomorphism. -/
instance sheafLowerShriek_componentCoproductHom_isIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m)) (Sheaf ((J m).toGrothendieck) (Type w))]
    (G : Sheaf ((J n).toGrothendieck) (Type w)) :
    IsIso (sheafLowerShriek_componentCoproductHom C J n m G) :=
  sorry

/-- Restriction of `g^{Sh}_{n!} G` to `C_m` is `∐_{φ : n ⟶ m} f_φ⁻¹ G`. -/
def sheafLowerShriek_componentCoproductIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m)) (Sheaf ((J m).toGrothendieck) (Type w))]
    (G : Sheaf ((J n).toGrothendieck) (Type w)) :
    (∐ fun φ : n ⟶ m =>
      ((C.map φ).toFunctor.sheafPullback (Type w)
        (J n).toGrothendieck (J m).toGrothendieck).obj G) ≅
      (stageRestrict C J (Type w) m).obj ((sheafLowerShriek C J n).obj G) :=
  asIso (sheafLowerShriek_componentCoproductHom C J n m G)

/-- The coproduct inclusion of `f_φ⁻¹ G` followed by the comparison is the component map. -/
theorem sheafLowerShriek_componentCoproduct_ι (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m)) (Sheaf ((J m).toGrothendieck) (Type w))]
    (G : Sheaf ((J n).toGrothendieck) (Type w)) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
        ((C.map ψ).toFunctor.sheafPullback (Type w)
          (J n).toGrothendieck (J m).toGrothendieck).obj G) φ ≫
      (sheafLowerShriek_componentCoproductIso C J n m G).hom =
      sheafLowerShriek_component C J φ G :=
  sorry

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]

/-- Inverse image `f_φ⁻¹` of abelian sheaves along a simplex operator `φ : n ⟶ m`. -/
abbrev abelianStageFacePullback {n m : SimplexCategory} (φ : n ⟶ m) :
    Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} ⥤
      Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w} :=
  (C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
    (J n).toGrothendieck (J m).toGrothendieck

/-- `abelianStageFacePullback φ` is sheaf pullback of abelian sheaves along `u_φ`. -/
theorem abelianStageFacePullback_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    abelianStageFacePullback C J φ =
      (C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck :=
  sorry

/-- The canonical component map `f_φ⁻¹ G ⟶ (g_{n!} G)_m` of abelian sheaves. -/
def abelianLowerShriek_component {n m : SimplexCategory} (φ : n ⟶ m)
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :
    ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
      (J n).toGrothendieck (J m).toGrothendieck).obj G ⟶
      (stageRestrict C J AddCommGrpCat.{w} m).obj ((abelianLowerShriek C J n).obj G) :=
  (((C.map φ).toFunctor.sheafAdjunctionContinuous AddCommGrpCat.{w}
      (J n).toGrothendieck (J m).toGrothendieck).homEquiv
    G ((stageRestrict C J AddCommGrpCat.{w} m).obj
      ((abelianLowerShriek C J n).obj G))).symm
  ((abelianLowerShriek_adjunction C J n).unit.app G ≫
    (sheafPushforwardContinuousNatTrans (stageInclusionWhisker C φ) AddCommGrpCat.{w}
        (J n).toGrothendieck (topology C J)).app ((abelianLowerShriek C J n).obj G) ≫
    (sheafPushforwardContinuousComp (C.map φ).toFunctor (ofStage C m) AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck (topology C J)).inv.app
      ((abelianLowerShriek C J n).obj G))

/-- The direct-sum comparison morphism
`∐_{φ : n ⟶ m} f_φ⁻¹ G ⟶ (g_{n!} G)_m` of abelian sheaves. -/
def abelianLowerShriek_componentBiproductHom (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :
    (∐ fun φ : n ⟶ m =>
      ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck).obj G) ⟶
      (stageRestrict C J AddCommGrpCat.{w} m).obj ((abelianLowerShriek C J n).obj G) :=
  Sigma.desc fun φ => abelianLowerShriek_component C J φ G

/-- The abelian comparison is the coproduct of the abelian component maps. -/
theorem abelianLowerShriek_componentBiproductHom_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :
    abelianLowerShriek_componentBiproductHom C J n m G =
      Sigma.desc fun φ => abelianLowerShriek_component C J φ G :=
  sorry

/-- The abelian direct-sum comparison morphism is an isomorphism. -/
instance abelianLowerShriek_componentBiproductHom_isIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :
    IsIso (abelianLowerShriek_componentBiproductHom C J n m G) :=
  sorry

/-- Restriction of `g_{n!} G` to `C_m` is `⊕_{φ : n ⟶ m} f_φ⁻¹ G`. -/
def abelianLowerShriek_componentBiproductIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :
    (∐ fun φ : n ⟶ m =>
      ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck).obj G) ≅
      (stageRestrict C J AddCommGrpCat.{w} m).obj ((abelianLowerShriek C J n).obj G) :=
  asIso (abelianLowerShriek_componentBiproductHom C J n m G)

/-- The direct-sum inclusion of `f_φ⁻¹ G` followed by the comparison is the component map. -/
theorem abelianLowerShriek_componentBiproduct_ι (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
        ((C.map ψ).toFunctor.sheafPullback AddCommGrpCat.{w}
          (J n).toGrothendieck (J m).toGrothendieck).obj G) φ ≫
      (abelianLowerShriek_componentBiproductIso C J n m G).hom =
      abelianLowerShriek_component C J φ G :=
  sorry

end CategoryTheory.SimplicialSites
