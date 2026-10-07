module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap87.Lemma_87_34_6_Over

/-!
# Comparison of étale slices of a formal algebraic space

The small étale site of algebraic spaces on the reduction of a formal
algebraic space `X` is compared with the category of étale morphisms of
formal algebraic spaces into `X`. The forward functor sends `φ : U ⟶ X`
to the fibre product `U ×_X X_red`. The inverse sends `ψ : V ⟶ X_red` to
the functor of points whose value on a scheme `T` is a pair `(a, b)` with
`a : T ⟶ X` and `b` a map `T ×_{a,X} X_red ⟶ V` over `X_red`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MorphismProperty Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}
variable {X : (Over S)ᵒᵖ ⥤ Type u}

/-- The Yoneda section of a `T`-point of `X`. -/
def yonedaSection {T : (Over S)ᵒᵖ} (a : X.obj T) : yoneda.obj T.unop ⟶ X :=
  yonedaEquiv.symm a

/-- `yonedaSection a` is the inverse Yoneda bijection of `a`. -/
theorem yonedaSection_def {T : (Over S)ᵒᵖ} (a : X.obj T) :
    yonedaSection a = yonedaEquiv.symm a :=
  rfl

variable [IsFormalAlgebraicSpace X] [RX : Reduction X]

/-- The Yoneda pullback of the reduction thickening along a `T`-point of `X` is
a thickening of algebraic spaces. -/
instance instIsThickening_yonedaSection {T : (Over S)ᵒᵖ} (a : X.obj T) :
    AlgebraicSpace.IsThickening
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom RX.representable
        (yonedaSection a)) :=
  RX.isThickening (yonedaSection a)

/-- Representability of the fibre product `T ×_{a,X} X_red` as a scheme over
`S`, extracted from the closed-immersion property of the reduction thickening. -/
theorem fibreRepresentable {T : (Over S)ᵒᵖ} (a : X.obj T) :
    yoneda.relativelyRepresentable
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom RX.representable
        (yonedaSection a)) :=
  (inferInstance :
      AlgebraicSpace.IsClosedImmersion
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom RX.representable
          (yonedaSection a))).presheaf.1

/-- The scheme over `S` representing `T ×_{a,X} X_red`. -/
def fibreScheme {T : (Over S)ᵒᵖ} (a : X.obj T) : Over S :=
  (fibreRepresentable a).pullback (𝟙 (yoneda.obj T.unop))

/-- `fibreScheme a` is the representing object of the Yoneda pullback of the
reduction thickening along `yonedaSection a`. -/
theorem fibreScheme_def {T : (Over S)ᵒᵖ} (a : X.obj T) :
    fibreScheme a = (fibreRepresentable a).pullback (𝟙 (yoneda.obj T.unop)) :=
  rfl

/-- Cone compatibility for the inverse identification of `fibreScheme a` with
`T ×_{a,X} X_red`. -/
theorem fibreSchemeIso_inv_w {T : (Over S)ᵒᵖ} (a : X.obj T) :
    𝟙 (pullback (yonedaSection a) (reductionι X)) ≫
      AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom RX.representable
        (yonedaSection a) =
      AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom RX.representable
        (yonedaSection a) ≫ 𝟙 (yoneda.obj T.unop) :=
  sorry

/-- The representing scheme of `T ×_{a,X} X_red` is identified, after Yoneda,
with the fibre product of `yonedaSection a` and the reduction thickening. -/
def fibreSchemeIso {T : (Over S)ᵒᵖ} (a : X.obj T) :
    yoneda.obj (fibreScheme a) ≅ pullback (yonedaSection a) (reductionι X) where
  hom := (fibreRepresentable a).fst (𝟙 (yoneda.obj T.unop))
  inv :=
    PullbackCone.IsLimit.lift
      ((fibreRepresentable a).isPullback (𝟙 (yoneda.obj T.unop))).isLimit
      (𝟙 _)
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom RX.representable
        (yonedaSection a))
      (fibreSchemeIso_inv_w a)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `fibreSchemeIso a` is the representing first projection. -/
@[simp]
theorem fibreSchemeIso_hom {T : (Over S)ᵒᵖ} (a : X.obj T) :
    (fibreSchemeIso a).hom = (fibreRepresentable a).fst (𝟙 (yoneda.obj T.unop)) :=
  rfl

/-- Naturality of Yoneda sections against restriction of test objects. -/
theorem yonedaSection_map {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : X.obj T) :
    yonedaSection (X.map f a) ≫ 𝟙 X =
      yoneda.map f.unop ≫ yonedaSection a :=
  sorry

/-- The identity square on the reduction thickening. -/
theorem reductionι_id_comp :
    𝟙 (reduction X).functorOfPoints ≫ reductionι X = reductionι X ≫ 𝟙 X :=
  sorry

/-- Comparison of Yoneda pullbacks of the reduction thickening along a
restriction of test objects. -/
def fibreSchemeMap_pullback {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : X.obj T) :
    pullback (yonedaSection (X.map f a)) (reductionι X) ⟶
      pullback (yonedaSection a) (reductionι X) :=
  pullback.map (yonedaSection (X.map f a)) (reductionι X) (yonedaSection a)
    (reductionι X) (yoneda.map f.unop) (𝟙 _) (𝟙 _)
    (yonedaSection_map f a) reductionι_id_comp

/-- Cone compatibility for the representing-scheme comparison. -/
theorem fibreSchemeMap_lift_w {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : X.obj T) :
    ((fibreRepresentable (X.map f a)).fst (𝟙 (yoneda.obj T'.unop)) ≫
        fibreSchemeMap_pullback f a) ≫
      AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom RX.representable
        (yonedaSection a) =
      yoneda.map
        ((fibreRepresentable (X.map f a)).snd (𝟙 (yoneda.obj T'.unop)) ≫
          f.unop) ≫
        𝟙 (yoneda.obj T.unop) :=
  sorry

/-- Restriction of representing schemes of fibre products along a morphism of
test objects. -/
def fibreSchemeMap {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : X.obj T) :
    fibreScheme (X.map f a) ⟶ fibreScheme a :=
  (fibreRepresentable a).lift
    ((fibreRepresentable (X.map f a)).fst (𝟙 (yoneda.obj T'.unop)) ≫
      fibreSchemeMap_pullback f a)
    ((fibreRepresentable (X.map f a)).snd (𝟙 (yoneda.obj T'.unop)) ≫ f.unop)
    (fibreSchemeMap_lift_w f a)

/-- `fibreSchemeMap f a` is a morphism of representing schemes over `S`. -/
theorem fibreSchemeMap_w {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : X.obj T) :
    (fibreSchemeMap f a).left ≫ (fibreScheme a).hom =
      (fibreScheme (X.map f a)).hom :=
  sorry

/-- A `T`-point of the inverse functor of Lemma 87.34.6: a map `a : T ⟶ X`
together with a map from the representing scheme of `T ×_{a,X} X_red` into
`V` that commutes with `ψ : V ⟶ X_red`. -/
structure ExtensionPoint (V : AlgebraicSpace.spacesEtaleSite (reduction X))
    (T : (Over S)ᵒᵖ) where
  /-- The underlying map `T ⟶ X`. -/
  toX : X.obj T
  /-- The map from the representing scheme of `T ×_{a,X} X_red` into `V`. -/
  toV : V.left.functorOfPoints.obj (op (fibreScheme toX))
  /-- The map into `V` lies over `X_red`. -/
  commutes :
    V.hom.app (op (fibreScheme toX)) toV =
      yonedaEquiv
        ((fibreRepresentable toX).fst (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd (yonedaSection toX) (reductionι X))

/-- Package a commuting pair as an `ExtensionPoint`. -/
def ExtensionPoint.ofSection (V : AlgebraicSpace.spacesEtaleSite (reduction X))
    {T : (Over S)ᵒᵖ} (a : X.obj T)
    (b : V.left.functorOfPoints.obj (op (fibreScheme a)))
    (h : V.hom.app (op (fibreScheme a)) b =
      yonedaEquiv
        ((fibreRepresentable a).fst (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd (yonedaSection a) (reductionι X))) :
    ExtensionPoint V T :=
  ⟨a, b, h⟩

/-- The first component of `ExtensionPoint.ofSection` is the given map to `X`. -/
@[simp]
theorem ExtensionPoint.ofSection_toX (V : AlgebraicSpace.spacesEtaleSite (reduction X))
    {T : (Over S)ᵒᵖ} (a : X.obj T)
    (b : V.left.functorOfPoints.obj (op (fibreScheme a)))
    (h : V.hom.app (op (fibreScheme a)) b =
      yonedaEquiv
        ((fibreRepresentable a).fst (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd (yonedaSection a) (reductionι X))) :
    (ExtensionPoint.ofSection V a b h).toX = a :=
  rfl

/-- The second component of `ExtensionPoint.ofSection` is the given map into
`V`. -/
@[simp]
theorem ExtensionPoint.ofSection_toV (V : AlgebraicSpace.spacesEtaleSite (reduction X))
    {T : (Over S)ᵒᵖ} (a : X.obj T)
    (b : V.left.functorOfPoints.obj (op (fibreScheme a)))
    (h : V.hom.app (op (fibreScheme a)) b =
      yonedaEquiv
        ((fibreRepresentable a).fst (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd (yonedaSection a) (reductionι X))) :
    (ExtensionPoint.ofSection V a b h).toV = b :=
  rfl

/-- Restriction of an `ExtensionPoint` along a morphism of test objects. -/
def ExtensionPoint.restrict {V : AlgebraicSpace.spacesEtaleSite (reduction X)}
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (p : ExtensionPoint V T) :
    ExtensionPoint V T' where
  toX := X.map f p.toX
  toV := V.left.functorOfPoints.map (op (fibreSchemeMap f p.toX)) p.toV
  commutes := sorry

/-- The first component of `ExtensionPoint.restrict` is restriction of `toX`. -/
@[simp]
theorem ExtensionPoint.restrict_toX {V : AlgebraicSpace.spacesEtaleSite (reduction X)}
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (p : ExtensionPoint V T) :
    (p.restrict f).toX = X.map f p.toX :=
  rfl

/-- The inverse object `U_{V,ψ}` of Lemma 87.34.6, as a functor of points. -/
def extensionAlong (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := ExtensionPoint V T
  map f := ofHom (fun p ↦ p.restrict f)
  map_id := sorry
  map_comp := sorry

/-- On objects, `extensionAlong V` is the type of `ExtensionPoint`s. -/
theorem extensionAlong_obj (V : AlgebraicSpace.spacesEtaleSite (reduction X))
    (T : (Over S)ᵒᵖ) : (extensionAlong V).obj T = ExtensionPoint V T :=
  rfl

/-- The map `T ×_{a,X} X_red ⟶ V` carried by a `T`-point of `U_{V,ψ}`,
transported along `fibreSchemeIso`. -/
def extensionAlong_toPullback (V : AlgebraicSpace.spacesEtaleSite (reduction X))
    {T : (Over S)ᵒᵖ} (p : (extensionAlong V).obj T) :
    pullback (yonedaSection p.toX) (reductionι X) ⟶ V.left.functorOfPoints :=
  (fibreSchemeIso p.toX).inv ≫ yonedaEquiv.symm p.toV

/-- Transporting a `T`-point along `fibreSchemeIso` recovers the representing
scheme map into `V`. -/
theorem extensionAlong_toPullback_comp {V : AlgebraicSpace.spacesEtaleSite (reduction X)}
    {T : (Over S)ᵒᵖ} (p : (extensionAlong V).obj T) :
    (fibreSchemeIso p.toX).hom ≫ extensionAlong_toPullback V p =
      yonedaEquiv.symm p.toV :=
  sorry

/-- A `T`-point of `extensionAlong V` is a pair `(a, b)` with `a : T ⟶ X` and
`b : T ×_{a,X} X_red ⟶ V` over `X_red`, transported along `fibreSchemeIso`. -/
theorem extensionAlong_spec (V : AlgebraicSpace.spacesEtaleSite (reduction X))
    {T : (Over S)ᵒᵖ} (p : (extensionAlong V).obj T) :
    extensionAlong_toPullback V p ≫ V.hom =
      pullback.snd (yonedaSection p.toX) (reductionι X) :=
  sorry

/-- The structure morphism `U_{V,ψ} ⟶ X`, sending `(a, b)` to `a`. -/
def extensionHom (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    extensionAlong V ⟶ X where
  app T := ofHom (fun p ↦ p.toX)
  naturality := sorry

/-- Components of `extensionHom V` are first projections of `ExtensionPoint`s. -/
@[simp]
theorem extensionHom_app (V : AlgebraicSpace.spacesEtaleSite (reduction X))
    {T : (Over S)ᵒᵖ} (p : (extensionAlong V).obj T) :
    (extensionHom V).app T p = p.toX :=
  sorry

/-- `extensionAlong V` is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_extensionAlong
    (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    IsFormalAlgebraicSpace (extensionAlong V) :=
  sorry

/-- The structure morphism `extensionHom V` is étale. -/
instance instEtale_extensionHom
    (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    Etale (extensionHom V) :=
  sorry

/-- Postcomposition on the `V`-component of an `ExtensionPoint`. -/
def extensionAlongMap {V W : AlgebraicSpace.spacesEtaleSite (reduction X)}
    (f : V ⟶ W) : extensionAlong V ⟶ extensionAlong W where
  app T := ofHom fun p ↦
    { toX := p.toX
      toV := f.left.app (op (fibreScheme p.toX)) p.toV
      commutes := sorry }
  naturality := sorry

/-- On first components, `extensionAlongMap` is the identity. -/
@[simp]
theorem extensionAlongMap_toX {V W : AlgebraicSpace.spacesEtaleSite (reduction X)}
    (f : V ⟶ W) {T : (Over S)ᵒᵖ} (p : (extensionAlong V).obj T) :
    ((extensionAlongMap f).app T p).toX = p.toX :=
  sorry

/-- The quasi-inverse sending `ψ : V ⟶ X_red` to `U_{V,ψ} ⟶ X`. -/
def ofSpacesEtale :
    AlgebraicSpace.spacesEtaleSite (reduction X) ⥤ EtaleOver X where
  obj V := EtaleOver.mk (extensionHom V)
  map f := ⟨MorphismProperty.Over.homMk (extensionAlongMap f) sorry trivial⟩
  map_id := sorry
  map_comp := sorry

/-- On objects, `ofSpacesEtale` is `EtaleOver.mk` of `extensionHom`. -/
@[simp]
theorem ofSpacesEtale_obj (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    ofSpacesEtale.obj V = EtaleOver.mk (extensionHom V) :=
  rfl


/-- The identity functor does not change the domain of an étale slice object. -/
instance instIsFormalAlgebraicSpace_id_obj (U : EtaleOver X) :
    IsFormalAlgebraicSpace ((𝟭 ((Over S)ᵒᵖ ⥤ Type u)).obj U.obj.left) :=
  U.property

/-- The codomain of an étale slice object is the standing formal algebraic space
`X`. -/
instance instIsFormalAlgebraicSpace_fromPUnit_obj (U : EtaleOver X) :
    IsFormalAlgebraicSpace ((Functor.fromPUnit X).obj U.obj.right) :=
  inferInstanceAs (IsFormalAlgebraicSpace X)

/-- The reduction of the standing formal algebraic space `X` is inherited by the
comma codomain. -/
instance instReduction_fromPUnit_obj (U : EtaleOver X) :
    Reduction ((Functor.fromPUnit X).obj U.obj.right) :=
  RX

/-- The induced map of reductions of an étale slice object is étale. -/
instance instEtale_reductionMap_etaleOver (U : EtaleOver X) :
    AlgebraicSpace.Etale (reductionMap U.obj.hom) :=
  instEtale_reductionMap U.obj.hom

/-- An étale-slice morphism over `X` is a morphism of domains over `X`. -/
theorem toSpacesEtale_map_w {U V : EtaleOver X} (f : U ⟶ V) :
    U.obj.hom ≫ 𝟙 X = f.hom.left ≫ V.obj.hom :=
  sorry

/-- The induced map of fibre products `U ×_X X_red ⟶ V ×_X X_red` lies over
`X_red`. -/
theorem toSpacesEtale_homMk_w {U V : EtaleOver X} (f : U ⟶ V) :
    pullback.map (reductionι X) U.obj.hom (reductionι X) V.obj.hom
        (𝟙 _) f.hom.left (𝟙 _) reductionι_id_comp (toSpacesEtale_map_w f) ≫
      reductionMap V.obj.hom =
      reductionMap U.obj.hom :=
  sorry

/-- The forward functor sending `φ : U ⟶ X` to `U ×_X X_red` étale over `X_red`. -/
def toSpacesEtale :
    EtaleOver X ⥤ AlgebraicSpace.spacesEtaleSite (reduction X) where
  obj U := MorphismProperty.Over.mk ⊤ (reductionMap U.obj.hom)
    (instEtale_reductionMap_etaleOver U)
  map {U V} f :=
    MorphismProperty.Over.homMk
      (pullback.map (reductionι X) U.obj.hom (reductionι X) V.obj.hom
        (𝟙 _) f.hom.left (𝟙 _) reductionι_id_comp (toSpacesEtale_map_w f))
      (toSpacesEtale_homMk_w f) trivial
  map_id := sorry
  map_comp := sorry

/-- On objects, `toSpacesEtale` is `Over.mk` of `reductionMap`. -/
theorem toSpacesEtale_obj (U : EtaleOver X) :
    toSpacesEtale.obj U =
      MorphismProperty.Over.mk ⊤ (reductionMap U.obj.hom)
        (instEtale_reductionMap_etaleOver U) :=
  rfl

/-- The underlying algebraic space of `toSpacesEtale.obj U` is
`reductionAlong U.obj.hom`. -/
@[simp]
theorem toSpacesEtale_obj_left (U : EtaleOver X) :
    (toSpacesEtale.obj U).left = reductionAlong U.obj.hom :=
  rfl

/-- The structural morphism of `toSpacesEtale.obj U` is
`reductionMap U.obj.hom`. -/
@[simp]
theorem toSpacesEtale_obj_hom (U : EtaleOver X) :
    (toSpacesEtale.obj U).hom = reductionMap U.obj.hom :=
  rfl

/-- Compatibility of the two paths from `T ×_{a,X} X_red` to `X` used in the
unit comparison. -/
theorem unitHomApp_lift_w (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (u : U.obj.left.obj T) :
    ((fibreRepresentable (U.obj.hom.app T u)).fst (𝟙 (yoneda.obj T.unop)) ≫
        pullback.snd (yonedaSection (U.obj.hom.app T u)) (reductionι X)) ≫
      reductionι X =
      ((fibreRepresentable (U.obj.hom.app T u)).fst (𝟙 (yoneda.obj T.unop)) ≫
        pullback.fst (yonedaSection (U.obj.hom.app T u)) (reductionι X) ≫
          yonedaEquiv.symm u) ≫
      U.obj.hom :=
  sorry

/-- The unit comparison identifies the induced map into `U ×_X X_red` with the
reduction projection. -/
theorem unitHomApp_commutes (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (u : U.obj.left.obj T) :
    (toSpacesEtale.obj U).hom.app (op (fibreScheme (U.obj.hom.app T u)))
        (yonedaEquiv
          (pullback.lift (f := reductionι X) (g := U.obj.hom)
            ((fibreRepresentable (U.obj.hom.app T u)).fst
                (𝟙 (yoneda.obj T.unop)) ≫
              pullback.snd (yonedaSection (U.obj.hom.app T u)) (reductionι X))
            ((fibreRepresentable (U.obj.hom.app T u)).fst
                (𝟙 (yoneda.obj T.unop)) ≫
              pullback.fst (yonedaSection (U.obj.hom.app T u)) (reductionι X) ≫
                yonedaEquiv.symm u)
            (unitHomApp_lift_w U u))) =
      yonedaEquiv
        ((fibreRepresentable (U.obj.hom.app T u)).fst
            (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd (yonedaSection (U.obj.hom.app T u)) (reductionι X)) :=
  sorry

/-- The forward comparison map of the unit, on `T`-points. -/
def unitHomApp (U : EtaleOver X) {T : (Over S)ᵒᵖ} (u : U.obj.left.obj T) :
    ExtensionPoint (toSpacesEtale.obj U) T :=
  let a := U.obj.hom.app T u
  let ξU : yoneda.obj T.unop ⟶ U.obj.left := yonedaEquiv.symm u
  let fst :=
    (fibreRepresentable a).fst (𝟙 (yoneda.obj T.unop))
  let lift :
      yoneda.obj (fibreScheme a) ⟶ (toSpacesEtale.obj U).left.functorOfPoints :=
    pullback.lift (f := reductionι X) (g := U.obj.hom)
      (fst ≫ pullback.snd (yonedaSection a) (reductionι X))
      (fst ≫ pullback.fst (yonedaSection a) (reductionι X) ≫ ξU)
      (unitHomApp_lift_w U u)
  { toX := a
    toV := yonedaEquiv lift
    commutes := unitHomApp_commutes U u }

/-- The unit comparison `U ⟶ U_{U ×_X X_red}` as a morphism of functors of
points. -/
def unitHom (U : EtaleOver X) :
    U.obj.left ⟶ extensionAlong (toSpacesEtale.obj U) where
  app T := ofHom fun u ↦ unitHomApp U u
  naturality := sorry

/-- Compatibility of the Yoneda section of `p.toX` with the `U`-leg of `p.toV`
along the reduction thickening. -/
theorem unitInvApp_inner_w (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint (toSpacesEtale.obj U) T) :
    (yonedaEquiv.symm p.toV ≫ pullback.snd (reductionι X) U.obj.hom) ≫
        U.obj.hom =
      yoneda.map ((fibreRepresentable p.toX).snd (𝟙 (yoneda.obj T.unop))) ≫
        yonedaSection p.toX :=
  sorry

/-- The étale lifting square for the inverse unit comparison: the `U`-leg of
`p.toV` lifts `p.toX` along the thickening `fibreScheme p.toX ⟶ T`. -/
theorem unitInvApp_sq (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint (toSpacesEtale.obj U) T) :
    CommSq
      (yonedaEquiv.symm p.toV ≫ pullback.snd (reductionι X) U.obj.hom)
      (yoneda.map ((fibreRepresentable p.toX).snd (𝟙 (yoneda.obj T.unop))))
      U.obj.hom (yonedaSection p.toX) :=
  ⟨unitInvApp_inner_w U p⟩

/-- The Yoneda pullback of `U.obj.hom` along `p.toX` receives the `U`-leg of
`p.toV` over the thickening. -/
def unitInvApp_liftUV (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint (toSpacesEtale.obj U) T) :
    yoneda.obj (fibreScheme p.toX) ⟶
      pullback U.obj.hom (yonedaSection p.toX) :=
  pullback.lift
    (yonedaEquiv.symm p.toV ≫ pullback.snd (reductionι X) U.obj.hom)
    (yoneda.map ((fibreRepresentable p.toX).snd (𝟙 (yoneda.obj T.unop))))
    (unitInvApp_inner_w U p)

/-- The `U`-leg of `unitInvApp_liftUV` is the `U`-component of `p.toV`. -/
theorem unitInvApp_liftUV_fst (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint (toSpacesEtale.obj U) T) :
    unitInvApp_liftUV U p ≫ pullback.fst U.obj.hom (yonedaSection p.toX) =
      yonedaEquiv.symm p.toV ≫ pullback.snd (reductionι X) U.obj.hom :=
  sorry

/-- The étale lifting square along the thickening admits a lift. -/
theorem unitInvApp_hasLift (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint (toSpacesEtale.obj U) T) :
    (unitInvApp_sq U p).HasLift :=
  sorry

/-- The inverse unit comparison, on `T`-points: the unique lift of `p.toX`
through `U.obj.hom` along the thickening `fibreScheme p.toX ⟶ T`
determined by `p.toV`. -/
def unitInvApp (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint (toSpacesEtale.obj U) T) : U.obj.left.obj T :=
  yonedaEquiv ((unitInvApp_sq U p).lift (hsq := unitInvApp_hasLift U p))

/-- The unique étale lift is inverse to the unit comparison on `T`-points. -/
theorem unitInvApp_spec (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint (toSpacesEtale.obj U) T) :
    unitHomApp U (unitInvApp U p) = p :=
  sorry

/-- The unit comparison followed by the inverse lift is the identity on `T`-points. -/
theorem unitInvApp_unitHomApp (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (u : U.obj.left.obj T) :
    unitInvApp U (unitHomApp U u) = u :=
  sorry

/-- The inverse unit comparison as a morphism of functors of points. -/
def unitInv (U : EtaleOver X) :
    extensionAlong (toSpacesEtale.obj U) ⟶ U.obj.left where
  app T := ofHom fun p ↦ unitInvApp U p
  naturality := sorry

/-- The unit isomorphism of the étale-slice equivalence, at an object `U`. -/
def unitIsoApp (U : EtaleOver X) :
    U ≅ ofSpacesEtale.obj (toSpacesEtale.obj U) where
  hom := ⟨MorphismProperty.Over.homMk (unitHom U) sorry trivial⟩
  inv := ⟨MorphismProperty.Over.homMk (unitInv U) sorry trivial⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The unit isomorphism of the étale-slice equivalence. -/
def unitIso : 𝟭 (EtaleOver X) ≅ toSpacesEtale ⋙ ofSpacesEtale :=
  NatIso.ofComponents (fun U ↦ unitIsoApp U) sorry

/-- A `T`-point of `X_red` that agrees with a `T`-point of `X` in `X` yields a
map into the Yoneda pullback of the reduction thickening. -/
theorem counitHomApp_inner_w
    (V : AlgebraicSpace.spacesEtaleSite (reduction X)) {T : (Over S)ᵒᵖ}
    (q : (reductionAlong (extensionHom V)).functorOfPoints.obj T) :
    𝟙 (yoneda.obj T.unop) ≫
        yonedaSection
          ((pullback.snd (reductionι X) (extensionHom V)).app T q).toX =
      yonedaEquiv.symm
          ((pullback.fst (reductionι X) (extensionHom V)).app T q) ≫
        reductionι X :=
  sorry

/-- The resulting cone on the Yoneda pullback of the reduction thickening is
compatible with the representing object `fibreScheme`. -/
theorem counitHomApp_lift_w
    (V : AlgebraicSpace.spacesEtaleSite (reduction X)) {T : (Over S)ᵒᵖ}
    (q : (reductionAlong (extensionHom V)).functorOfPoints.obj T) :
    pullback.lift (𝟙 (yoneda.obj T.unop))
        (yonedaEquiv.symm
          ((pullback.fst (reductionι X) (extensionHom V)).app T q))
        (counitHomApp_inner_w V q) ≫
      AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom RX.representable
        (yonedaSection
          ((pullback.snd (reductionι X) (extensionHom V)).app T q).toX) =
      yoneda.map (𝟙 T.unop) ≫ 𝟙 (yoneda.obj T.unop) :=
  sorry

/-- The counit comparison `(U_{V,ψ} ×_X X_red) ⟶ V`, on `T`-points. -/
def counitHomApp (V : AlgebraicSpace.spacesEtaleSite (reduction X))
    {T : (Over S)ᵒᵖ}
    (q : (reductionAlong (extensionHom V)).functorOfPoints.obj T) :
    V.left.functorOfPoints.obj T :=
  let p : ExtensionPoint V T :=
    (pullback.snd (reductionι X) (extensionHom V)).app T q
  let xred := (pullback.fst (reductionι X) (extensionHom V)).app T q
  let toFibre : T.unop ⟶ fibreScheme p.toX :=
    (fibreRepresentable p.toX).lift
      (pullback.lift (𝟙 (yoneda.obj T.unop)) (yonedaEquiv.symm xred)
        (counitHomApp_inner_w V q))
      (𝟙 T.unop) (counitHomApp_lift_w V q)
  V.left.functorOfPoints.map (op toFibre) p.toV

/-- The counit comparison as a morphism of algebraic spaces. -/
def counitHom (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    reductionAlong (extensionHom V) ⟶ V.left where
  app T := ofHom fun q ↦ counitHomApp V q
  naturality := sorry

/-- A `V`-point over `X_red` remains over `X_red` after restriction along
`T ×_{a,X} X_red ⟶ T`. -/
theorem counitInvApp_commutes
    (V : AlgebraicSpace.spacesEtaleSite (reduction X)) {T : (Over S)ᵒᵖ}
    (v : V.left.functorOfPoints.obj T) :
    V.hom.app
        (op (fibreScheme ((reductionι X).app T (V.hom.app T v))))
        (V.left.functorOfPoints.map
          (op
            ((fibreRepresentable ((reductionι X).app T (V.hom.app T v))).snd
              (𝟙 (yoneda.obj T.unop))))
          v) =
      yonedaEquiv
        ((fibreRepresentable ((reductionι X).app T (V.hom.app T v))).fst
            (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd
            (yonedaSection ((reductionι X).app T (V.hom.app T v)))
            (reductionι X)) :=
  sorry

/-- The pair `(ψ(v), U_{V,ψ}-point of v)` lies in the fibre product over `X`. -/
theorem counitInvApp_lift_w
    (V : AlgebraicSpace.spacesEtaleSite (reduction X)) {T : (Over S)ᵒᵖ}
    (v : V.left.functorOfPoints.obj T) :
    (ofHom fun (_ : ULift.{u} PUnit) ↦ V.hom.app T v) ≫
        (reductionι X).app T =
      (ofHom fun _ ↦
        ({ toX := (reductionι X).app T (V.hom.app T v)
           toV :=
             V.left.functorOfPoints.map
               (op
                 ((fibreRepresentable
                     ((reductionι X).app T (V.hom.app T v))).snd
                   (𝟙 (yoneda.obj T.unop))))
               v
           commutes := counitInvApp_commutes V v } : ExtensionPoint V T)) ≫
        (extensionHom V).app T :=
  sorry

/-- A point of the fibre product `U_{V,ψ} ×_X X_red` assembled from a `V`-point
that already factors through `X_red`. -/
def counitInvApp (V : AlgebraicSpace.spacesEtaleSite (reduction X))
    {T : (Over S)ᵒᵖ} (v : V.left.functorOfPoints.obj T) :
    (reductionAlong (extensionHom V)).functorOfPoints.obj T :=
  let xred := V.hom.app T v
  let a := (reductionι X).app T xred
  let p : ExtensionPoint V T :=
    { toX := a
      toV :=
        V.left.functorOfPoints.map
          (op ((fibreRepresentable a).snd (𝟙 (yoneda.obj T.unop)))) v
      commutes := counitInvApp_commutes V v }
  (pullbackObjIso (reductionι X) (extensionHom V) T).inv
    (pullback.lift (ofHom fun (_ : ULift.{u} PUnit) ↦ xred)
      (ofHom fun _ ↦ p) (counitInvApp_lift_w V v) ⟨⟨⟩⟩)

/-- The inverse counit comparison as a morphism of algebraic spaces. -/
def counitInv (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    V.left ⟶ reductionAlong (extensionHom V) where
  app T := ofHom fun v ↦ counitInvApp V v
  naturality := sorry

/-- The counit isomorphism of algebraic spaces `U_{V,ψ} ×_X X_red ≅ V`. -/
def counitSpaceIso (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    (toSpacesEtale.obj (ofSpacesEtale.obj V)).left ≅ V.left where
  hom := counitHom V
  inv := counitInv V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The counit isomorphism of the étale-slice equivalence, at an object `V`. -/
def counitIsoApp (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    toSpacesEtale.obj (ofSpacesEtale.obj V) ≅ V :=
  MorphismProperty.Over.isoMk (counitSpaceIso V) sorry

/-- The counit isomorphism of the étale-slice equivalence. -/
def counitIso :
    ofSpacesEtale ⋙ toSpacesEtale ≅ 𝟭 (AlgebraicSpace.spacesEtaleSite (reduction X)) :=
  NatIso.ofComponents (fun V ↦ counitIsoApp V) sorry

end AlgebraicGeometry.FormalAlgebraicSpace
