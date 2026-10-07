module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import stacks_project.Chap59.Lemma_59_80_9_Pullback
public import stacks_project.Chap63.«63_4_0_2_LowerShriekPresheaf»
public import stacks_project.Chap63.Lemma_63_4_2_StalkCoproduct
public import stacks_project.Chap63.Remark_63_4_9_Stalk

/-!
# Cartesian base change of finite-support data

For a cartesian square of schemes, locally closed finite supports on `X_V` pull
back to `X'_{V'}`, and geometric points of `X'` over `ȳ'` correspond to geometric
points of `X` over `ȳ = g ∘ ȳ'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)

/-- The scheme morphism `X'_{V'} ⟶ X_V` induced by a cartesian square and the
étale base change of `V` along `g`. -/
def cartesianBaseChangeSchemeMap (V : Y.Etale) :
    baseChangeScheme f' ((smallEtalePullback g).obj V) ⟶ baseChangeScheme f V :=
  have hw := h_cart.w
  pullback.lift
    (baseChangeToBase f' ((smallEtalePullback g).obj V) ≫ pullback.fst V.hom g)
    (baseChangeToSource f' ((smallEtalePullback g).obj V) ≫ g')
    sorry

/-- The first projection of `cartesianBaseChangeSchemeMap` is the base-change
map of `V` along `g`. -/
theorem cartesianBaseChangeSchemeMap_fst (V : Y.Etale) :
    cartesianBaseChangeSchemeMap f g f' g' h_cart V ≫ baseChangeToBase f V =
      baseChangeToBase f' ((smallEtalePullback g).obj V) ≫ pullback.fst V.hom g :=
  sorry

/-- The second projection of `cartesianBaseChangeSchemeMap` is `g'` on the
source of `X'_{V'}`. -/
theorem cartesianBaseChangeSchemeMap_snd (V : Y.Etale) :
    cartesianBaseChangeSchemeMap f g f' g' h_cart V ≫ baseChangeToSource f V =
      baseChangeToSource f' ((smallEtalePullback g).obj V) ≫ g' :=
  sorry

/-- The open of `X'_{V'}` lying over an open of `X_V` along the cartesian
scheme map. -/
def cartesianBaseChangeOpenHom (V : Y.Etale) (U : (baseChangeScheme f V).Opens) :
    (cartesianBaseChangeSchemeMap f g f' g' h_cart V ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι
    ((cartesianBaseChangeSchemeMap f g f' g' h_cart V ⁻¹ᵁ U).ι ≫
      cartesianBaseChangeSchemeMap f g f' g' h_cart V)
    sorry

/-- The source bijection `{f'(x̄') = ȳ'} ≃ {f(x̄) = ȳ}` induced by `g'`, where
`ȳ = g ∘ ȳ'`. -/
def Over.baseChangeEquiv (ybar' : GeometricPoint Y') :
    Over f' ybar' ≃ Over f (imageGeometricPoint g ybar') where
  toFun x' := ⟨x'.toScheme ≫ g', sorry⟩
  invFun x := ⟨h_cart.lift x.toScheme ybar'.hom sorry, sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `Over.baseChangeEquiv` composes with `g'`. -/
theorem Over.baseChangeEquiv_apply (ybar' : GeometricPoint Y')
    (x' : Over f' ybar') :
    (Over.baseChangeEquiv f g f' g' h_cart ybar' x').toScheme = x'.toScheme ≫ g' :=
  sorry

/-- The pair `(x̄, ȳ')` lies over the cartesian square. -/
theorem Over.baseChangeEquiv_lift_w (ybar' : GeometricPoint Y')
    (x : Over f (imageGeometricPoint g ybar')) :
    x.toScheme ≫ f = ybar'.hom ≫ g :=
  sorry

/-- The inverse of `Over.baseChangeEquiv` is the cartesian lift of `(x̄, ȳ')`. -/
theorem Over.baseChangeEquiv_symm_apply (ybar' : GeometricPoint Y')
    (x : Over f (imageGeometricPoint g ybar')) :
    ((Over.baseChangeEquiv f g f' g' h_cart ybar').symm x).toScheme =
      h_cart.lift x.toScheme ybar'.hom
        (Over.baseChangeEquiv_lift_w f g ybar' x) :=
  sorry

/-- The image of a lifted point of `X'` under `g'` recovers the original point of
`X` over `ȳ`. -/
theorem Over.baseChangeEquiv_symm_toGeometricPoint (ybar' : GeometricPoint Y')
    (x : Over f (imageGeometricPoint g ybar')) :
    imageGeometricPoint g'
        ((Over.baseChangeEquiv f g f' g' h_cart ybar').symm x).toGeometricPoint =
      x.toGeometricPoint :=
  sorry

namespace FiniteSupport

variable [LocallyQuasiFinite f] [LocallyQuasiFinite f']

/-- Inverse image of an admissible support along `X'_{V'} ⟶ X_V`. -/
def Admissible.baseChange {V : Y.Etale} (A : Admissible f V) :
    Admissible f' ((smallEtalePullback g).obj V) where
  subset := ⟨cartesianBaseChangeSchemeMap f g f' g' h_cart V ⁻¹' A.subset, sorry⟩
  ambient := cartesianBaseChangeSchemeMap f g f' g' h_cart V ⁻¹ᵁ A.ambient
  subset_le_ambient := sorry
  isClosed_in_ambient := sorry
  toBase_isFinite := sorry

/-- Base change of an admissible support is inverse image of the locally closed
subset and of the ambient open. -/
theorem Admissible.baseChange_spec {V : Y.Etale} (A : Admissible f V) :
    ((Admissible.baseChange f g f' g' h_cart A).subset :
        Set (baseChangeScheme f' ((smallEtalePullback g).obj V))) =
      cartesianBaseChangeSchemeMap f g f' g' h_cart V ⁻¹' A.subset ∧
      (Admissible.baseChange f g f' g' h_cart A).ambient =
        cartesianBaseChangeSchemeMap f g f' g' h_cart V ⁻¹ᵁ A.ambient :=
  sorry

/-- Base change of admissible supports is monotone. -/
theorem Admissible.baseChange_mono {V : Y.Etale} {A B : Admissible f V}
    (h : A ≤ B) :
    Admissible.baseChange f g f' g' h_cart A ≤
      Admissible.baseChange f g f' g' h_cart B :=
  sorry

/-- The functor on admissible supports induced by inverse image along
`X'_{V'} ⟶ X_V`. -/
def Admissible.baseChangeFunctor (V : Y.Etale) :
    Admissible f V ⥤ Admissible f' ((smallEtalePullback g).obj V) where
  obj := Admissible.baseChange f g f' g' h_cart
  map h := CategoryTheory.homOfLE (Admissible.baseChange_mono f g f' g' h_cart (leOfHom h))
  map_id := sorry
  map_comp := sorry

/-- The base-change functor acts by inverse image of admissible supports. -/
theorem Admissible.baseChangeFunctor_obj (V : Y.Etale) (A : Admissible f V) :
    (Admissible.baseChangeFunctor f g f' g' h_cart V).obj A =
      Admissible.baseChange f g f' g' h_cart A :=
  sorry

/-- The morphism of small-étale `X'`-schemes from the inverse-image ambient open
to the étale pullback of the original ambient open along `g'`. -/
def ambientBaseChangeHom {V : Y.Etale} (A : Admissible f V) :
    mk ((Admissible.baseChange f g f' g' h_cart A).ambient.ι ≫
          baseChangeToSource f' ((smallEtalePullback g).obj V)) ⟶
      (smallEtalePullback g').obj (mk (A.ambient.ι ≫ baseChangeToSource f V)) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      (cartesianBaseChangeOpenHom f g f' g' h_cart V A.ambient)
      ((Admissible.baseChange f g f' g' h_cart A).ambient.ι ≫
        baseChangeToSource f' ((smallEtalePullback g).obj V))
      sorry)
    sorry

/-- Pullback of supported sections `H_Z(F) ⟶ H_{Z'}((g')⁻¹ F)` along the
cartesian square. -/
def sectionsBaseChange (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (A : Admissible f V) :
    sections f F A ⟶
      sections f' ((etaleAbelianSheafPullback g').obj F)
        (Admissible.baseChange f g f' g' h_cart A) :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        ⟨((((etaleAbelianSheafPullback g').obj F).1.map
                (ambientBaseChangeHom f g f' g' h_cart A).op).hom
            (((((smallEtalePullback g').sheafAdjunctionContinuous AddCommGrpCat.{u}
                    X.smallEtaleTopology X'.smallEtaleTopology).unit.app F).hom.app
                (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).hom σ.1)),
          sorry⟩
      map_zero' := sorry
      map_add' := sorry }

/-- The finite-support diagram map sending `H_Z(F)` to `H_{Z'}((g')⁻¹ F)`. -/
def sectionsBaseChangeNatTrans (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    diagram f F V ⟶
      Admissible.baseChangeFunctor f g f' g' h_cart V ⋙
        diagram f' ((etaleAbelianSheafPullback g').obj F)
          ((smallEtalePullback g).obj V) where
  app A := sectionsBaseChange f g f' g' h_cart F A
  naturality := sorry

end FiniteSupport

variable [LocallyQuasiFinite f] [LocallyQuasiFinite f']

/-- The base change of a finite-support pair `(Z, s)` along the cartesian
square. -/
def FiniteSupportTerm.baseChange {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    {V : Y.Etale} (t : FiniteSupportTerm f F V) :
    FiniteSupportTerm f' ((etaleAbelianSheafPullback g').obj F)
      ((smallEtalePullback g).obj V) where
  subscheme := pullback t.ι (cartesianBaseChangeSchemeMap f g f' g' h_cart V)
  ι := pullback.snd t.ι (cartesianBaseChangeSchemeMap f g f' g' h_cart V)
  ι_isImmersion := sorry
  toBase_isFinite := sorry
  ambient := cartesianBaseChangeSchemeMap f g f' g' h_cart V ⁻¹ᵁ t.ambient
  range_subset_ambient := sorry
  isClosed_in_ambient := sorry
  sec :=
    ((FiniteSupport.sectionsBaseChange f g f' g' h_cart F
          (FiniteSupport.Admissible.ofTerm f t)).hom
        ⟨t.sec, t.mem_sectionsSupportedIn⟩).1
  mem_sectionsSupportedIn := sorry

/-- A base-changed finite-support pair records the pullback immersion and the
inverse-image ambient open. -/
theorem FiniteSupportTerm.baseChange_spec
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} {V : Y.Etale}
    (t : FiniteSupportTerm f F V) :
    (FiniteSupportTerm.baseChange f g f' g' h_cart t).ι =
        pullback.snd t.ι (cartesianBaseChangeSchemeMap f g f' g' h_cart V) ∧
      (FiniteSupportTerm.baseChange f g f' g' h_cart t).ambient =
        cartesianBaseChangeSchemeMap f g f' g' h_cart V ⁻¹ᵁ t.ambient :=
  sorry

/-- The stalk identification `F_x̄ ≅ ((g')⁻¹ F)_{x̄'}` on a summand of the fibre
coproduct, for `x̄'` the cartesian lift of `x̄`. -/
def abelianStalkCoproductBaseChangeIso_summand (ybar' : GeometricPoint Y')
    [∀ x' : Over f' ybar',
      InitiallySmall
        ((smallEtalePullback g' ⋙
            (toSmallEtalePoint x'.toGeometricPoint).fiber).Elements)]
    [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
    [HasProducts.{u} AddCommGrpCat.{u}]
    (x : Over f (imageGeometricPoint g ybar'))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint
          ((Over.baseChangeEquiv f g f' g' h_cart ybar').symm x).toGeometricPoint).sheafFiber.obj
        ((etaleAbelianSheafPullback g').obj F) ≅
      (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F :=
  (pullbackSheafFiberIso g'
        ((Over.baseChangeEquiv f g f' g' h_cart ybar').symm x).toGeometricPoint F).symm ≪≫
    eqToIso
      (congrArg (fun p : GeometricPoint X ↦
          (toSmallEtalePoint p).sheafFiber.obj F)
        (Over.baseChangeEquiv_symm_toGeometricPoint f g f' g' h_cart ybar' x))

/-- Reindexing `⊕_{f(x̄)=ȳ} F_x̄` along `Over.baseChangeEquiv` and identifying
summands by `pullbackSheafFiberIso`. -/
def abelianStalkCoproductBaseChangeIso (ybar' : GeometricPoint Y')
    [∀ x' : Over f' ybar',
      InitiallySmall
        ((smallEtalePullback g' ⋙
            (toSmallEtalePoint x'.toGeometricPoint).fiber).Elements)]
    [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
    [HasProducts.{u} AddCommGrpCat.{u}] :
    abelianStalkCoproduct f (imageGeometricPoint g ybar') ≅
      etaleAbelianSheafPullback g' ⋙ abelianStalkCoproduct f' ybar' :=
  NatIso.ofComponents
    (fun F ↦
      Sigma.whiskerEquiv (Over.baseChangeEquiv f g f' g' h_cart ybar').symm
        (fun x ↦
          abelianStalkCoproductBaseChangeIso_summand f g f' g' h_cart ybar' x F))
    sorry

/-- Evaluating the fibre-coproduct base-change isomorphism recovers
`Sigma.whiskerEquiv` of the summand identifications. -/
theorem abelianStalkCoproductBaseChangeIso_app (ybar' : GeometricPoint Y')
    [∀ x' : Over f' ybar',
      InitiallySmall
        ((smallEtalePullback g' ⋙
            (toSmallEtalePoint x'.toGeometricPoint).fiber).Elements)]
    [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
    [HasProducts.{u} AddCommGrpCat.{u}]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkCoproductBaseChangeIso f g f' g' h_cart ybar').app F =
      Sigma.whiskerEquiv (Over.baseChangeEquiv f g f' g' h_cart ybar').symm
        (fun x ↦
          abelianStalkCoproductBaseChangeIso_summand f g f' g' h_cart ybar' x F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
