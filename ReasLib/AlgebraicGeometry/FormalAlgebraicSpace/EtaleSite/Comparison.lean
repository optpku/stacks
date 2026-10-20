module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Etale

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

namespace AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

variable {S : Scheme.{u}}
variable {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
variable (R : ReductionData X)

/-- Representability of the fibre product `T ×_{a,X} X_red` as a scheme over
`S`, extracted from the closed-immersion property of the reduction thickening. -/
theorem fibreRepresentable {T : (Over S)ᵒᵖ} (a : X.obj T) :
    yoneda.relativelyRepresentable
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom R.representable
        (yonedaEquiv.symm a)) :=
  (R.isThickening (yonedaEquiv.symm a)).1.presheaf.1

/-- The scheme over `S` representing `T ×_{a,X} X_red`. -/
def fibreScheme {T : (Over S)ᵒᵖ} (a : X.obj T) : Over S :=
  (fibreRepresentable R a).pullback (𝟙 (yoneda.obj T.unop))

/-- `fibreScheme R a` is the representing object of the Yoneda pullback of the
reduction thickening along `yonedaEquiv.symm a`. -/
theorem fibreScheme_def {T : (Over S)ᵒᵖ} (a : X.obj T) :
    fibreScheme R a = (fibreRepresentable R a).pullback (𝟙 (yoneda.obj T.unop)) :=
  rfl

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Cone compatibility for the inverse identification of `fibreScheme R a` with
`T ×_{a,X} X_red`. -/
private theorem fibreSchemeIso_inv_w {T : (Over S)ᵒᵖ} (a : X.obj T) :
    𝟙 (pullback (yonedaEquiv.symm a) (R.ι)) ≫
      AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom R.representable
        (yonedaEquiv.symm a) =
      AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom R.representable
        (yonedaEquiv.symm a) ≫ 𝟙 (yoneda.obj T.unop) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The representing projection followed by its inverse is the identity. -/
private theorem fibreSchemeIso_hom_inv_id {T : (Over S)ᵒᵖ} (a : X.obj T) :
    (fibreRepresentable R a).fst (𝟙 (yoneda.obj T.unop)) ≫ (PullbackCone.IsLimit.lift
      ((fibreRepresentable R a).isPullback (𝟙 (yoneda.obj T.unop))).isLimit
      (𝟙 _)
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom R.representable
        (yonedaEquiv.symm a))
      (fibreSchemeIso_inv_w R a)) = 𝟙 (yoneda.obj (fibreScheme R a)) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The inverse representing projection followed by the projection is the identity. -/
private theorem fibreSchemeIso_inv_hom_id {T : (Over S)ᵒᵖ} (a : X.obj T) :
    (PullbackCone.IsLimit.lift
      ((fibreRepresentable R a).isPullback (𝟙 (yoneda.obj T.unop))).isLimit
      (𝟙 _)
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom R.representable
        (yonedaEquiv.symm a))
      (fibreSchemeIso_inv_w R a)) ≫ (fibreRepresentable R a).fst (𝟙 (yoneda.obj T.unop)) =
      𝟙 (pullback (yonedaEquiv.symm a) R.ι) :=
  sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The representing scheme of `T ×_{a,X} X_red` is identified, after Yoneda,
with the fibre product of `yonedaEquiv.symm a` and the reduction thickening. -/
def fibreSchemeIso {T : (Over S)ᵒᵖ} (a : X.obj T) :
    yoneda.obj (fibreScheme R a) ≅ pullback (yonedaEquiv.symm a) (R.ι) where
  hom := (fibreRepresentable R a).fst (𝟙 (yoneda.obj T.unop))
  inv :=
    PullbackCone.IsLimit.lift
      ((fibreRepresentable R a).isPullback (𝟙 (yoneda.obj T.unop))).isLimit
      (𝟙 _)
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom R.representable
        (yonedaEquiv.symm a))
      (fibreSchemeIso_inv_w R a)
  hom_inv_id := fibreSchemeIso_hom_inv_id R a
  inv_hom_id := fibreSchemeIso_inv_hom_id R a

/-- The forward map of `fibreSchemeIso R a` is the representing first projection. -/
@[simp]
theorem fibreSchemeIso_hom {T : (Over S)ᵒᵖ} (a : X.obj T) :
    (fibreSchemeIso R a).hom = (fibreRepresentable R a).fst (𝟙 (yoneda.obj T.unop)) :=
  rfl

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Naturality of Yoneda sections against restriction of test objects. -/
private theorem yonedaSection_map {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : X.obj T) :
    yonedaEquiv.symm (X.map f a) ≫ 𝟙 X =
      yoneda.map f.unop ≫ yonedaEquiv.symm a :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The identity square on the reduction thickening. -/
private theorem reductionι_id_comp :
    𝟙 R.space.functorOfPoints ≫ R.ι = R.ι ≫ 𝟙 X := by
  simp only [Category.id_comp, Category.comp_id]

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Comparison of Yoneda pullbacks of the reduction thickening along a
restriction of test objects. -/
private def fibreSchemeMap_pullback {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : X.obj T) :
    pullback (yonedaEquiv.symm (X.map f a)) (R.ι) ⟶
      pullback (yonedaEquiv.symm a) (R.ι) :=
  pullback.map (yonedaEquiv.symm (X.map f a)) (R.ι) (yonedaEquiv.symm a)
    (R.ι) (yoneda.map f.unop) (𝟙 _) (𝟙 _)
    (yonedaSection_map f a) (reductionι_id_comp R)

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Cone compatibility for the representing-scheme comparison. -/
private theorem fibreSchemeMap_lift_w {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : X.obj T) :
    ((fibreRepresentable R (X.map f a)).fst (𝟙 (yoneda.obj T'.unop)) ≫
        fibreSchemeMap_pullback R f a) ≫
      AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom R.representable
        (yonedaEquiv.symm a) =
      yoneda.map
        ((fibreRepresentable R (X.map f a)).snd (𝟙 (yoneda.obj T'.unop)) ≫
          f.unop) ≫
        𝟙 (yoneda.obj T.unop) :=
  sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- Restriction of representing schemes of fibre products along a morphism of
test objects. -/
def fibreSchemeMap {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : X.obj T) :
    fibreScheme R (X.map f a) ⟶ fibreScheme R a :=
  (fibreRepresentable R a).lift
    ((fibreRepresentable R (X.map f a)).fst (𝟙 (yoneda.obj T'.unop)) ≫
      fibreSchemeMap_pullback R f a)
    ((fibreRepresentable R (X.map f a)).snd (𝟙 (yoneda.obj T'.unop)) ≫ f.unop)
    (fibreSchemeMap_lift_w R f a)

/-- A commuting pair consisting of a map `a : T ⟶ X`
together with a map from the representing scheme of `T ×_{a,X} X_red` into
`V` that commutes with `ψ : V ⟶ X_red`. -/
structure ExtensionPoint (V : AlgebraicSpace.spacesEtaleSite R.space)
    (T : (Over S)ᵒᵖ) where
  /-- The underlying map `T ⟶ X`. -/
  toX : X.obj T
  /-- The map from the representing scheme of `T ×_{a,X} X_red` into `V`. -/
  toV : V.left.functorOfPoints.obj (op (fibreScheme R toX))
  /-- The map into `V` lies over `X_red`. -/
  commutes :
    V.hom.app (op (fibreScheme R toX)) toV =
      yonedaEquiv
        ((fibreRepresentable R toX).fst (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd (yonedaEquiv.symm toX) (R.ι))

/-- Package a commuting pair as an `ExtensionPoint R`. -/
def ExtensionPoint.ofSection (V : AlgebraicSpace.spacesEtaleSite R.space)
    {T : (Over S)ᵒᵖ} (a : X.obj T)
    (b : V.left.functorOfPoints.obj (op (fibreScheme R a)))
    (h : V.hom.app (op (fibreScheme R a)) b =
      yonedaEquiv
        ((fibreRepresentable R a).fst (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd (yonedaEquiv.symm a) (R.ι))) :
    ExtensionPoint R V T :=
  ⟨a, b, h⟩

/-- The first component of `ExtensionPoint.ofSection R` is the given map to `X`. -/
@[simp]
theorem ExtensionPoint.ofSection_toX (V : AlgebraicSpace.spacesEtaleSite R.space)
    {T : (Over S)ᵒᵖ} (a : X.obj T)
    (b : V.left.functorOfPoints.obj (op (fibreScheme R a)))
    (h : V.hom.app (op (fibreScheme R a)) b =
      yonedaEquiv
        ((fibreRepresentable R a).fst (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd (yonedaEquiv.symm a) (R.ι))) :
    (ExtensionPoint.ofSection R V a b h).toX = a :=
  rfl

/-- The second component of `ExtensionPoint.ofSection R` is the given map into
`V`. -/
@[simp]
theorem ExtensionPoint.ofSection_toV (V : AlgebraicSpace.spacesEtaleSite R.space)
    {T : (Over S)ᵒᵖ} (a : X.obj T)
    (b : V.left.functorOfPoints.obj (op (fibreScheme R a)))
    (h : V.hom.app (op (fibreScheme R a)) b =
      yonedaEquiv
        ((fibreRepresentable R a).fst (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd (yonedaEquiv.symm a) (R.ι))) :
    (ExtensionPoint.ofSection R V a b h).toV = b :=
  rfl

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Restriction of a commuting pair remains over the reduction. -/
private theorem ExtensionPoint.restrict_commutes
    {V : AlgebraicSpace.spacesEtaleSite R.space} {T T' : (Over S)ᵒᵖ}
    (f : T ⟶ T') (p : ExtensionPoint R V T) :
    V.hom.app (op (fibreScheme R (X.map f p.toX)))
      (V.left.functorOfPoints.map (op (fibreSchemeMap R f p.toX)) p.toV) =
      yonedaEquiv ((fibreRepresentable R (X.map f p.toX)).fst
        (𝟙 (yoneda.obj T'.unop)) ≫ pullback.snd (yonedaEquiv.symm (X.map f p.toX)) R.ι) :=
  sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- Restriction of an `ExtensionPoint R` along a morphism of test objects. -/
def ExtensionPoint.restrict {V : AlgebraicSpace.spacesEtaleSite R.space}
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (p : ExtensionPoint R V T) :
    ExtensionPoint R V T' where
  toX := X.map f p.toX
  toV := V.left.functorOfPoints.map (op (fibreSchemeMap R f p.toX)) p.toV
  commutes := ExtensionPoint.restrict_commutes R f p

/-- The first component of `ExtensionPoint.restrict R` is restriction of `toX`. -/
@[simp]
theorem ExtensionPoint.restrict_toX {V : AlgebraicSpace.spacesEtaleSite R.space}
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (p : ExtensionPoint R V T) :
    (ExtensionPoint.restrict R f p).toX = X.map f p.toX :=
  rfl

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Restricting an extension point along an identity is the identity. -/
private theorem extensionAlong_map_id (V : AlgebraicSpace.spacesEtaleSite R.space)
    (T : (Over S)ᵒᵖ) :
    (ofHom (fun p : ExtensionPoint R V T ↦ ExtensionPoint.restrict R (𝟙 T) p)) =
      𝟙 (ExtensionPoint R V T) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Successive restrictions agree with restriction along a composite. -/
private theorem extensionAlong_map_comp (V : AlgebraicSpace.spacesEtaleSite R.space)
    {T T' T'' : (Over S)ᵒᵖ} (f : T ⟶ T') (g : T' ⟶ T'') :
    (ofHom (fun p : ExtensionPoint R V T ↦ ExtensionPoint.restrict R (f ≫ g) p)) =
      (ofHom (fun p : ExtensionPoint R V T ↦ ExtensionPoint.restrict R f p)) ≫
      (ofHom (fun p : ExtensionPoint R V T' ↦ ExtensionPoint.restrict R g p)) :=
  sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The extension presheaf of an algebraic space étale over the reduction. -/
def extensionAlong (V : AlgebraicSpace.spacesEtaleSite R.space) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := ExtensionPoint R V T
  map f := ofHom (fun p ↦ ExtensionPoint.restrict R f p)
  map_id := extensionAlong_map_id R V
  map_comp := extensionAlong_map_comp R V

/-- On objects, `extensionAlong R V` is the type of `ExtensionPoint R`s. -/
theorem extensionAlong_obj (V : AlgebraicSpace.spacesEtaleSite R.space)
    (T : (Over S)ᵒᵖ) : (extensionAlong R V).obj T = ExtensionPoint R V T :=
  rfl

/-- The map `T ×_{a,X} X_red ⟶ V` carried by a `T`-point of `U_{V,ψ}`,
transported along `fibreSchemeIso R`. -/
def extensionAlong_toPullback (V : AlgebraicSpace.spacesEtaleSite R.space)
    {T : (Over S)ᵒᵖ} (p : (extensionAlong R V).obj T) :
    pullback (yonedaEquiv.symm p.toX) (R.ι) ⟶ V.left.functorOfPoints :=
  (fibreSchemeIso R p.toX).inv ≫ yonedaEquiv.symm p.toV

/-- Transporting a `T`-point along `fibreSchemeIso R` recovers the representing
scheme map into `V`. -/
theorem extensionAlong_toPullback_comp {V : AlgebraicSpace.spacesEtaleSite R.space}
    {T : (Over S)ᵒᵖ} (p : (extensionAlong R V).obj T) :
    (fibreSchemeIso R p.toX).hom ≫ extensionAlong_toPullback R V p =
      yonedaEquiv.symm p.toV :=
  sorry

/-- A `T`-point of `extensionAlong R V` is a pair `(a, b)` with `a : T ⟶ X` and
`b : T ×_{a,X} X_red ⟶ V` over `X_red`, transported along `fibreSchemeIso R`. -/
theorem extensionAlong_spec (V : AlgebraicSpace.spacesEtaleSite R.space)
    {T : (Over S)ᵒᵖ} (p : (extensionAlong R V).obj T) :
    extensionAlong_toPullback R V p ≫ V.hom =
      pullback.snd (yonedaEquiv.symm p.toX) (R.ι) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Projection to the base commutes with restriction of extension points. -/
private theorem extensionHom_naturality (V : AlgebraicSpace.spacesEtaleSite R.space)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (extensionAlong R V).map f ≫ (ofHom (fun p : ExtensionPoint R V T' ↦ p.toX)) =
      (ofHom (fun p : ExtensionPoint R V T ↦ p.toX)) ≫ X.map f := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The structure morphism `U_{V,ψ} ⟶ X`, sending `(a, b)` to `a`. -/
def extensionHom (V : AlgebraicSpace.spacesEtaleSite R.space) :
    extensionAlong R V ⟶ X where
  app _ := ofHom (fun p ↦ p.toX)
  naturality {_ _} g := extensionHom_naturality R V g

/-- Components of `extensionHom R V` are first projections of `ExtensionPoint R`s. -/
@[simp]
theorem extensionHom_app (V : AlgebraicSpace.spacesEtaleSite R.space)
    {T : (Over S)ᵒᵖ} (p : (extensionAlong R V).obj T) :
    (extensionHom R V).app T p = p.toX :=
  sorry

/-- `extensionAlong R V` is a formal algebraic space. -/
theorem extensionAlong_isFormalAlgebraicSpace
    (V : AlgebraicSpace.spacesEtaleSite R.space) :
    IsFormalAlgebraicSpace (extensionAlong R V) :=
  sorry

/-- The structure morphism `extensionHom R V` is étale. -/
theorem extensionHom_etale
    (V : AlgebraicSpace.spacesEtaleSite R.space) :
    Etale (extensionHom R V) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Postcomposition of the second component preserves the commuting condition. -/
private theorem extensionAlongMap_commutes {V W : AlgebraicSpace.spacesEtaleSite R.space}
    (f : V ⟶ W) {T : (Over S)ᵒᵖ} (p : ExtensionPoint R V T) :
    W.hom.app (op (fibreScheme R p.toX)) (f.left.app (op (fibreScheme R p.toX)) p.toV) =
      yonedaEquiv ((fibreRepresentable R p.toX).fst (𝟙 (yoneda.obj T.unop)) ≫
        pullback.snd (yonedaEquiv.symm p.toX) R.ι) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Postcomposition on commuting pairs is natural in the test scheme. -/
private theorem extensionAlongMap_naturality {V W : AlgebraicSpace.spacesEtaleSite R.space}
    (f : V ⟶ W) {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    (extensionAlong R V).map g ≫
      (ofHom fun p : ExtensionPoint R V T' ↦
        (⟨p.toX, f.left.app (op (fibreScheme R p.toX)) p.toV,
          extensionAlongMap_commutes R f p⟩ : ExtensionPoint R W T')) =
    (ofHom fun p : ExtensionPoint R V T ↦
        (⟨p.toX, f.left.app (op (fibreScheme R p.toX)) p.toV,
          extensionAlongMap_commutes R f p⟩ : ExtensionPoint R W T)) ≫
      (extensionAlong R W).map g := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- Postcomposition on the `V`-component of an `ExtensionPoint R`. -/
def extensionAlongMap {V W : AlgebraicSpace.spacesEtaleSite R.space}
    (f : V ⟶ W) : extensionAlong R V ⟶ extensionAlong R W where
  app _ := ofHom fun p ↦
    { toX := p.toX
      toV := f.left.app (op (fibreScheme R p.toX)) p.toV
      commutes := extensionAlongMap_commutes R f p }
  naturality {_ _} g := extensionAlongMap_naturality R f g

/-- On first components, `extensionAlongMap R` is the identity. -/
@[simp]
theorem extensionAlongMap_toX {V W : AlgebraicSpace.spacesEtaleSite R.space}
    (f : V ⟶ W) {T : (Over S)ᵒᵖ} (p : (extensionAlong R V).obj T) :
    ((extensionAlongMap R f).app T p).toX = p.toX :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Postcomposition of extension points commutes with projection to the base. -/
private theorem ofSpacesEtale_map_w {V W : AlgebraicSpace.spacesEtaleSite R.space}
    (f : V ⟶ W) : extensionAlongMap R f ≫ extensionHom R W = extensionHom R V := sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Extension sends identity morphisms to identity morphisms. -/
private theorem ofSpacesEtale_map_id (V : AlgebraicSpace.spacesEtaleSite R.space) :
    extensionAlongMap R (𝟙 V) = 𝟙 (extensionAlong R V) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Extension preserves composition of morphisms over the reduction. -/
private theorem ofSpacesEtale_map_comp {V W Z : AlgebraicSpace.spacesEtaleSite R.space}
    (f : V ⟶ W) (g : W ⟶ Z) :
    extensionAlongMap R (f ≫ g) = extensionAlongMap R f ≫ extensionAlongMap R g := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The quasi-inverse sending `ψ : V ⟶ X_red` to `U_{V,ψ} ⟶ X`. -/
def ofSpacesEtale :
    AlgebraicSpace.spacesEtaleSite R.space ⥤ EtaleOver X where
  obj V := EtaleOver.mk (hU := extensionAlong_isFormalAlgebraicSpace R V)
    (hφ := extensionHom_etale R V) (extensionHom R V)
  map f := ⟨MorphismProperty.Over.homMk (extensionAlongMap R f) (ofSpacesEtale_map_w R f) trivial⟩
  map_id V := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact ofSpacesEtale_map_id R V
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact ofSpacesEtale_map_comp R f g

/-- On objects, `ofSpacesEtale R` is `EtaleOver.mk` of `extensionHom R`. -/
@[simp]
theorem ofSpacesEtale_obj (V : AlgebraicSpace.spacesEtaleSite R.space) :
    (ofSpacesEtale R).obj V =
      EtaleOver.mk (hU := extensionAlong_isFormalAlgebraicSpace R V)
        (hφ := extensionHom_etale R V) (extensionHom R V) :=
  rfl


-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- An étale-slice morphism over `X` is a morphism of domains over `X`. -/
private theorem toSpacesEtale_map_w {U V : EtaleOver X} (f : U ⟶ V) :
    U.obj.hom ≫ 𝟙 X = f.hom.left ≫ V.obj.hom :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The induced map of fibre products `U ×_X X_red ⟶ V ×_X X_red` lies over
`X_red`. -/
private theorem toSpacesEtale_homMk_w {U V : EtaleOver X} (f : U ⟶ V) :
    pullback.map (R.ι) U.obj.hom (R.ι) V.obj.hom
        (𝟙 _) f.hom.left (𝟙 _) (reductionι_id_comp R) (toSpacesEtale_map_w f) ≫
      (etalePullbackProjection (X := V.obj.left) (Y := X) V.obj.hom R.space R.ι) =
      (etalePullbackProjection (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Pullback to the reduction preserves identity morphisms. -/
private theorem toSpacesEtale_map_id (U : EtaleOver X) :
    (MorphismProperty.Over.homMk
      (pullback.map R.ι U.obj.hom R.ι U.obj.hom (𝟙 _) (𝟙 U : U ⟶ U).hom.left (𝟙 _)
        (reductionι_id_comp R) (toSpacesEtale_map_w (𝟙 U)))
      (toSpacesEtale_homMk_w R (𝟙 U)) trivial :
      MorphismProperty.Over.mk ⊤ (etalePullbackProjection (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι)
        (etalePullback_etale (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι) ⟶
      MorphismProperty.Over.mk ⊤ (etalePullbackProjection (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι)
        (etalePullback_etale (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι)) =
      𝟙 (MorphismProperty.Over.mk ⊤ (etalePullbackProjection (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι)
        (etalePullback_etale (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι)) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Pullback to the reduction preserves composition. -/
private theorem toSpacesEtale_map_comp {U V W : EtaleOver X} (f : U ⟶ V) (g : V ⟶ W) :
    (MorphismProperty.Over.homMk
      (pullback.map R.ι U.obj.hom R.ι W.obj.hom (𝟙 _) (f ≫ g).hom.left (𝟙 _)
        (reductionι_id_comp R) (toSpacesEtale_map_w (f ≫ g)))
      (toSpacesEtale_homMk_w R (f ≫ g)) trivial :
      MorphismProperty.Over.mk ⊤ (etalePullbackProjection (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι)
        (etalePullback_etale (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι) ⟶
      MorphismProperty.Over.mk ⊤ (etalePullbackProjection (X := W.obj.left) (Y := X) W.obj.hom R.space R.ι)
        (etalePullback_etale (X := W.obj.left) (Y := X) W.obj.hom R.space R.ι)) =
    (MorphismProperty.Over.homMk
      (pullback.map R.ι U.obj.hom R.ι V.obj.hom
        (𝟙 _) f.hom.left (𝟙 _) (reductionι_id_comp R) (toSpacesEtale_map_w f))
      (toSpacesEtale_homMk_w R f) trivial :
      MorphismProperty.Over.mk ⊤ (etalePullbackProjection (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι)
        (etalePullback_etale (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι) ⟶
      MorphismProperty.Over.mk ⊤ (etalePullbackProjection (X := V.obj.left) (Y := X) V.obj.hom R.space R.ι)
        (etalePullback_etale (X := V.obj.left) (Y := X) V.obj.hom R.space R.ι)) ≫
    (MorphismProperty.Over.homMk
      (pullback.map R.ι V.obj.hom R.ι W.obj.hom (𝟙 _) g.hom.left (𝟙 _)
        (reductionι_id_comp R) (toSpacesEtale_map_w g))
      (toSpacesEtale_homMk_w R g) trivial :
      MorphismProperty.Over.mk ⊤ (etalePullbackProjection (X := V.obj.left) (Y := X) V.obj.hom R.space R.ι)
        (etalePullback_etale (X := V.obj.left) (Y := X) V.obj.hom R.space R.ι) ⟶
      MorphismProperty.Over.mk ⊤ (etalePullbackProjection (X := W.obj.left) (Y := X) W.obj.hom R.space R.ι)
        (etalePullback_etale (X := W.obj.left) (Y := X) W.obj.hom R.space R.ι)) :=
  sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The forward functor sending `φ : U ⟶ X` to `U ×_X X_red` étale over `X_red`. -/
def toSpacesEtale :
    EtaleOver X ⥤ AlgebraicSpace.spacesEtaleSite R.space where
  obj U := MorphismProperty.Over.mk ⊤ ((etalePullbackProjection (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι))
    (etalePullback_etale (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι)
  map {U V} f :=
    MorphismProperty.Over.homMk
      (pullback.map (R.ι) U.obj.hom (R.ι) V.obj.hom
        (𝟙 _) f.hom.left (𝟙 _) (reductionι_id_comp R) (toSpacesEtale_map_w f))
      (toSpacesEtale_homMk_w R f) trivial
  map_id := toSpacesEtale_map_id R
  map_comp := toSpacesEtale_map_comp R

/-- Pullback to the reduction has the pullback projection as its structure morphism. -/
theorem toSpacesEtale_obj (U : EtaleOver X) :
    (toSpacesEtale R).obj U =
      MorphismProperty.Over.mk ⊤ ((etalePullbackProjection (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι))
        (etalePullback_etale (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι) :=
  rfl

/-- The underlying algebraic space of the forward comparison is the étale pullback. -/
@[simp]
theorem toSpacesEtale_obj_left (U : EtaleOver X) :
    ((toSpacesEtale R).obj U).left = (etalePullback (X := U.obj.left) (Y := X) U.obj.hom (hf := U.obj.prop) R.space R.ι) :=
  rfl

/-- The structure morphism of the forward comparison is the projection to the reduction. -/
@[simp]
theorem toSpacesEtale_obj_hom (U : EtaleOver X) :
    ((toSpacesEtale R).obj U).hom = (etalePullbackProjection (X := U.obj.left) (Y := X) U.obj.hom R.space R.ι) :=
  rfl

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Compatibility of the two paths from `T ×_{a,X} X_red` to `X` used in the
unit comparison. -/
private theorem unitHomApp_lift_w (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (u : U.obj.left.obj T) :
    ((fibreRepresentable R (U.obj.hom.app T u)).fst (𝟙 (yoneda.obj T.unop)) ≫
        pullback.snd (yonedaEquiv.symm (U.obj.hom.app T u)) (R.ι)) ≫
      R.ι =
      ((fibreRepresentable R (U.obj.hom.app T u)).fst (𝟙 (yoneda.obj T.unop)) ≫
        pullback.fst (yonedaEquiv.symm (U.obj.hom.app T u)) (R.ι) ≫
          yonedaEquiv.symm u) ≫
      U.obj.hom :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The unit comparison identifies the induced map into `U ×_X X_red` with the
reduction projection. -/
private theorem unitHomApp_commutes (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (u : U.obj.left.obj T) :
    ((toSpacesEtale R).obj U).hom.app (op (fibreScheme R (U.obj.hom.app T u)))
        (yonedaEquiv
          (pullback.lift (f := R.ι) (g := U.obj.hom)
            ((fibreRepresentable R (U.obj.hom.app T u)).fst
                (𝟙 (yoneda.obj T.unop)) ≫
              pullback.snd (yonedaEquiv.symm (U.obj.hom.app T u)) (R.ι))
            ((fibreRepresentable R (U.obj.hom.app T u)).fst
                (𝟙 (yoneda.obj T.unop)) ≫
              pullback.fst (yonedaEquiv.symm (U.obj.hom.app T u)) (R.ι) ≫
                yonedaEquiv.symm u)
            (unitHomApp_lift_w R U u))) =
      yonedaEquiv
        ((fibreRepresentable R (U.obj.hom.app T u)).fst
            (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd (yonedaEquiv.symm (U.obj.hom.app T u)) (R.ι)) :=
  sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The forward comparison map of the unit, on `T`-points. -/
def unitHomApp (U : EtaleOver X) {T : (Over S)ᵒᵖ} (u : U.obj.left.obj T) :
    ExtensionPoint R ((toSpacesEtale R).obj U) T :=
  let a := U.obj.hom.app T u
  let ξU : yoneda.obj T.unop ⟶ U.obj.left := yonedaEquiv.symm u
  let fst :=
    (fibreRepresentable R a).fst (𝟙 (yoneda.obj T.unop))
  let lift :
      yoneda.obj (fibreScheme R a) ⟶ ((toSpacesEtale R).obj U).left.functorOfPoints :=
    pullback.lift (f := R.ι) (g := U.obj.hom)
      (fst ≫ pullback.snd (yonedaEquiv.symm a) (R.ι))
      (fst ≫ pullback.fst (yonedaEquiv.symm a) (R.ι) ≫ ξU)
      (unitHomApp_lift_w R U u)
  { toX := a
    toV := yonedaEquiv lift
    commutes := unitHomApp_commutes R U u }

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The pointwise comparison commutes with restriction of test schemes. -/
private theorem unitHom_naturality (U : EtaleOver X) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (U.obj.left).map f ≫ (ofHom fun p ↦ unitHomApp R U (T := T') p) =
      (ofHom fun p ↦ unitHomApp R U (T := T) p) ≫ (extensionAlong R ((toSpacesEtale R).obj U)).map f := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The unit comparison `U ⟶ U_{U ×_X X_red}` as a morphism of functors of
points. -/
def unitHom (U : EtaleOver X) :
    U.obj.left ⟶ extensionAlong R ((toSpacesEtale R).obj U) where
  app _ := ofHom fun u ↦ unitHomApp R U u
  naturality {_ _} g := unitHom_naturality R U g

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- Compatibility of the Yoneda section of `p.toX` with the `U`-leg of `p.toV`
along the reduction thickening. -/
private theorem unitInvApp_inner_w (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint R ((toSpacesEtale R).obj U) T) :
    (yonedaEquiv.symm p.toV ≫ pullback.snd (R.ι) U.obj.hom) ≫
        U.obj.hom =
      yoneda.map ((fibreRepresentable R p.toX).snd (𝟙 (yoneda.obj T.unop))) ≫
        yonedaEquiv.symm p.toX :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The étale lifting square for the inverse unit comparison: the `U`-leg of
`p.toV` lifts `p.toX` along the thickening `fibreScheme R p.toX ⟶ T`. -/
private theorem unitInvApp_sq (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint R ((toSpacesEtale R).obj U) T) :
    CommSq
      (yonedaEquiv.symm p.toV ≫ pullback.snd (R.ι) U.obj.hom)
      (yoneda.map ((fibreRepresentable R p.toX).snd (𝟙 (yoneda.obj T.unop))))
      U.obj.hom (yonedaEquiv.symm p.toX) :=
  ⟨unitInvApp_inner_w R U p⟩

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The étale lifting square along the thickening admits a lift. -/
private theorem unitInvApp_hasLift (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint R ((toSpacesEtale R).obj U) T) :
    (unitInvApp_sq R U p).HasLift :=
  sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The inverse unit comparison, on `T`-points: the unique lift of `p.toX`
through `U.obj.hom` along the thickening `fibreScheme R p.toX ⟶ T`
determined by `p.toV`. -/
def unitInvApp (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint R ((toSpacesEtale R).obj U) T) : U.obj.left.obj T :=
  yonedaEquiv ((unitInvApp_sq R U p).lift (hsq := unitInvApp_hasLift R U p))

/-- The unique étale lift is inverse to the unit comparison on `T`-points. -/
theorem unitInvApp_spec (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (p : ExtensionPoint R ((toSpacesEtale R).obj U) T) :
    unitHomApp R U (unitInvApp R U p) = p :=
  sorry

/-- The unit comparison followed by the inverse lift is the identity on `T`-points. -/
theorem unitInvApp_unitHomApp (U : EtaleOver X) {T : (Over S)ᵒᵖ}
    (u : U.obj.left.obj T) :
    unitInvApp R U (unitHomApp R U u) = u :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The pointwise comparison commutes with restriction of test schemes. -/
private theorem unitInv_naturality (U : EtaleOver X) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (extensionAlong R ((toSpacesEtale R).obj U)).map f ≫ (ofHom fun p ↦ unitInvApp R U (T := T') p) =
      (ofHom fun p ↦ unitInvApp R U (T := T) p) ≫ (U.obj.left).map f := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The inverse unit comparison as a morphism of functors of points. -/
def unitInv (U : EtaleOver X) :
    extensionAlong R ((toSpacesEtale R).obj U) ⟶ U.obj.left where
  app _ := ofHom fun p ↦ unitInvApp R U p
  naturality {_ _} g := unitInv_naturality R U g

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The unit map lies over the original formal space. -/
private theorem unitIsoApp_hom_w (U : EtaleOver X) :
    unitHom R U ≫ extensionHom R ((toSpacesEtale R).obj U) = U.obj.hom := sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The inverse unit map lies over the original formal space. -/
private theorem unitIsoApp_inv_w (U : EtaleOver X) :
    unitInv R U ≫ U.obj.hom = extensionHom R ((toSpacesEtale R).obj U) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The unit followed by its inverse is the identity in the formal étale slice. -/
private theorem unitIsoApp_hom_inv_id (U : EtaleOver X) :
    (⟨MorphismProperty.Over.homMk (unitHom R U) (unitIsoApp_hom_w R U) trivial⟩ : U ⟶ (ofSpacesEtale R).obj ((toSpacesEtale R).obj U)) ≫ (⟨MorphismProperty.Over.homMk (unitInv R U) (unitIsoApp_inv_w R U) trivial⟩ : (ofSpacesEtale R).obj ((toSpacesEtale R).obj U) ⟶ U) = 𝟙 U := sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The inverse unit followed by the unit is the identity in the formal étale slice. -/
private theorem unitIsoApp_inv_hom_id (U : EtaleOver X) :
    (⟨MorphismProperty.Over.homMk (unitInv R U) (unitIsoApp_inv_w R U) trivial⟩ : (ofSpacesEtale R).obj ((toSpacesEtale R).obj U) ⟶ U) ≫ (⟨MorphismProperty.Over.homMk (unitHom R U) (unitIsoApp_hom_w R U) trivial⟩ : U ⟶ (ofSpacesEtale R).obj ((toSpacesEtale R).obj U)) = 𝟙 ((ofSpacesEtale R).obj ((toSpacesEtale R).obj U)) :=
  sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The unit isomorphism of the étale-slice equivalence, at an object `U`. -/
def unitIsoApp (U : EtaleOver X) :
    U ≅ (ofSpacesEtale R).obj ((toSpacesEtale R).obj U) where
  hom := ⟨MorphismProperty.Over.homMk (unitHom R U) (unitIsoApp_hom_w R U) trivial⟩
  inv := ⟨MorphismProperty.Over.homMk (unitInv R U) (unitIsoApp_inv_w R U) trivial⟩
  hom_inv_id := unitIsoApp_hom_inv_id R U
  inv_hom_id := unitIsoApp_inv_hom_id R U

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The unit isomorphisms are natural in formal spaces étale over the base. -/
private theorem unitIso_naturality {U V : EtaleOver X} (f : U ⟶ V) :
    f ≫ (unitIsoApp R V).hom =
      (unitIsoApp R U).hom ≫ ((toSpacesEtale R) ⋙ (ofSpacesEtale R)).map f := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The unit isomorphism of the étale-slice equivalence. -/
def unitIso : 𝟭 (EtaleOver X) ≅ (toSpacesEtale R) ⋙ (ofSpacesEtale R) :=
  NatIso.ofComponents (fun U ↦ unitIsoApp R U) (fun f ↦ unitIso_naturality R f)

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- A `T`-point of `X_red` that agrees with a `T`-point of `X` in `X` yields a
map into the Yoneda pullback of the reduction thickening. -/
private theorem counitHomApp_inner_w
    (V : AlgebraicSpace.spacesEtaleSite R.space) {T : (Over S)ᵒᵖ}
    (q : (((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).left).functorOfPoints.obj T) :
    𝟙 (yoneda.obj T.unop) ≫
        yonedaEquiv.symm
          ((pullback.snd (R.ι) (extensionHom R V)).app T q).toX =
      yonedaEquiv.symm
          ((pullback.fst (R.ι) (extensionHom R V)).app T q) ≫
        R.ι :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The resulting cone on the Yoneda pullback of the reduction thickening is
compatible with the representing object `fibreScheme R`. -/
private theorem counitHomApp_lift_w
    (V : AlgebraicSpace.spacesEtaleSite R.space) {T : (Over S)ᵒᵖ}
    (q : (((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).left).functorOfPoints.obj T) :
    pullback.lift (𝟙 (yoneda.obj T.unop))
        (yonedaEquiv.symm
          ((pullback.fst (R.ι) (extensionHom R V)).app T q))
        (counitHomApp_inner_w R V q) ≫
      AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom R.representable
        (yonedaEquiv.symm
          ((pullback.snd (R.ι) (extensionHom R V)).app T q).toX) =
      yoneda.map (𝟙 T.unop) ≫ 𝟙 (yoneda.obj T.unop) :=
  sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The counit comparison `(U_{V,ψ} ×_X X_red) ⟶ V`, on `T`-points. -/
def counitHomApp (V : AlgebraicSpace.spacesEtaleSite R.space)
    {T : (Over S)ᵒᵖ}
    (q : (((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).left).functorOfPoints.obj T) :
    V.left.functorOfPoints.obj T :=
  let p : ExtensionPoint R V T :=
    (pullback.snd (R.ι) (extensionHom R V)).app T q
  let xred := (pullback.fst (R.ι) (extensionHom R V)).app T q
  let toFibre : T.unop ⟶ fibreScheme R p.toX :=
    (fibreRepresentable R p.toX).lift
      (pullback.lift (𝟙 (yoneda.obj T.unop)) (yonedaEquiv.symm xred)
        (counitHomApp_inner_w R V q))
      (𝟙 T.unop) (counitHomApp_lift_w R V q)
  V.left.functorOfPoints.map (op toFibre) p.toV

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The pointwise comparison commutes with restriction of test schemes. -/
private theorem counitHom_naturality (V : AlgebraicSpace.spacesEtaleSite R.space) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).left.functorOfPoints).map f ≫ (ofHom fun p ↦ counitHomApp R V (T := T') p) =
      (ofHom fun p ↦ counitHomApp R V (T := T) p) ≫ (V.left.functorOfPoints).map f := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The counit comparison as a morphism of algebraic spaces. -/
def counitHom (V : AlgebraicSpace.spacesEtaleSite R.space) :
    ((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).left ⟶ V.left where
  app _ := ofHom fun q ↦ counitHomApp R V q
  naturality {_ _} g := counitHom_naturality R V g

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- A `V`-point over `X_red` remains over `X_red` after restriction along
`T ×_{a,X} X_red ⟶ T`. -/
private theorem counitInvApp_commutes
    (V : AlgebraicSpace.spacesEtaleSite R.space) {T : (Over S)ᵒᵖ}
    (v : V.left.functorOfPoints.obj T) :
    V.hom.app
        (op (fibreScheme R ((R.ι).app T (V.hom.app T v))))
        (V.left.functorOfPoints.map
          (op
            ((fibreRepresentable R ((R.ι).app T (V.hom.app T v))).snd
              (𝟙 (yoneda.obj T.unop))))
          v) =
      yonedaEquiv
        ((fibreRepresentable R ((R.ι).app T (V.hom.app T v))).fst
            (𝟙 (yoneda.obj T.unop)) ≫
          pullback.snd
            (yonedaEquiv.symm ((R.ι).app T (V.hom.app T v)))
            (R.ι)) :=
  sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The pair `(ψ(v), U_{V,ψ}-point of v)` lies in the fibre product over `X`. -/
private theorem counitInvApp_lift_w
    (V : AlgebraicSpace.spacesEtaleSite R.space) {T : (Over S)ᵒᵖ}
    (v : V.left.functorOfPoints.obj T) :
    (ofHom fun (_ : ULift.{u} PUnit) ↦ V.hom.app T v) ≫
        (R.ι).app T =
      (ofHom fun _ ↦
        ({ toX := (R.ι).app T (V.hom.app T v)
           toV :=
             V.left.functorOfPoints.map
               (op
                 ((fibreRepresentable R
                     ((R.ι).app T (V.hom.app T v))).snd
                   (𝟙 (yoneda.obj T.unop))))
               v
           commutes := counitInvApp_commutes R V v } : ExtensionPoint R V T)) ≫
        (extensionHom R V).app T :=
  sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- A point of the fibre product `U_{V,ψ} ×_X X_red` assembled from a `V`-point
that already factors through `X_red`. -/
def counitInvApp (V : AlgebraicSpace.spacesEtaleSite R.space)
    {T : (Over S)ᵒᵖ} (v : V.left.functorOfPoints.obj T) :
    (((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).left).functorOfPoints.obj T :=
  let xred := V.hom.app T v
  let a := (R.ι).app T xred
  let p : ExtensionPoint R V T :=
    { toX := a
      toV :=
        V.left.functorOfPoints.map
          (op ((fibreRepresentable R a).snd (𝟙 (yoneda.obj T.unop)))) v
      commutes := counitInvApp_commutes R V v }
  (pullbackObjIso (R.ι) (extensionHom R V) T).inv
    (pullback.lift (ofHom fun (_ : ULift.{u} PUnit) ↦ xred)
      (ofHom fun _ ↦ p) (counitInvApp_lift_w R V v) ⟨⟨⟩⟩)

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The pointwise comparison commutes with restriction of test schemes. -/
private theorem counitInv_naturality (V : AlgebraicSpace.spacesEtaleSite R.space) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (V.left.functorOfPoints).map f ≫ (ofHom fun p ↦ counitInvApp R V (T := T') p) =
      (ofHom fun p ↦ counitInvApp R V (T := T) p) ≫ (((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).left.functorOfPoints).map f := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The inverse counit comparison as a morphism of algebraic spaces. -/
def counitInv (V : AlgebraicSpace.spacesEtaleSite R.space) :
    V.left ⟶ ((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).left where
  app _ := ofHom fun v ↦ counitInvApp R V v
  naturality {_ _} g := counitInv_naturality R V g

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The counit followed by its inverse is the identity algebraic-space morphism. -/
private theorem counitSpaceIso_hom_inv_id (V : AlgebraicSpace.spacesEtaleSite R.space) :
    counitHom R V ≫ counitInv R V = 𝟙 ((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).left := sorry

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The inverse counit followed by the counit is the identity algebraic-space morphism. -/
private theorem counitSpaceIso_inv_hom_id (V : AlgebraicSpace.spacesEtaleSite R.space) :
    counitInv R V ≫ counitHom R V = 𝟙 V.left := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The counit isomorphism of algebraic spaces `U_{V,ψ} ×_X X_red ≅ V`. -/
def counitSpaceIso (V : AlgebraicSpace.spacesEtaleSite R.space) :
    ((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).left ≅ V.left where
  hom := counitHom R V
  inv := counitInv R V
  hom_inv_id := counitSpaceIso_hom_inv_id R V
  inv_hom_id := counitSpaceIso_inv_hom_id R V

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The counit isomorphism commutes with the maps to the reduction. -/
private theorem counitIsoApp_w (V : AlgebraicSpace.spacesEtaleSite R.space) :
    (counitSpaceIso R V).hom ≫ V.hom =
      ((toSpacesEtale R).obj ((ofSpacesEtale R).obj V)).hom := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The counit isomorphism of the étale-slice equivalence, at an object `V`. -/
def counitIsoApp (V : AlgebraicSpace.spacesEtaleSite R.space) :
    (toSpacesEtale R).obj ((ofSpacesEtale R).obj V) ≅ V :=
  MorphismProperty.Over.isoMk (counitSpaceIso R V) (counitIsoApp_w R V)

-- Local declaration justification (module visibility): export this private compatibility fact for the exposed constructions that use it.
set_option backward.privateInPublic true in
/-- The counit isomorphisms are natural in spaces étale over the reduction. -/
private theorem counitIso_naturality {V W : AlgebraicSpace.spacesEtaleSite R.space}
    (f : V ⟶ W) :
    ((ofSpacesEtale R) ⋙ (toSpacesEtale R)).map f ≫ (counitIsoApp R W).hom =
      (counitIsoApp R V).hom ≫ f := sorry

-- Local declaration justification (module visibility): the exposed construction uses private compatibility proofs.
set_option backward.privateInPublic true in
/-- The counit isomorphism of the étale-slice equivalence. -/
def counitIso :
    (ofSpacesEtale R) ⋙ (toSpacesEtale R) ≅ 𝟭 (AlgebraicSpace.spacesEtaleSite R.space) :=
  NatIso.ofComponents (fun V ↦ counitIsoApp R V) (fun f ↦ counitIso_naturality R f)

/-- Formal algebraic spaces representably étale over a formal space are equivalent
to algebraic spaces étale over its reduction. -/
def spacesEtaleEquiv : EtaleOver X ≌ AlgebraicSpace.spacesEtaleSite R.space :=
  CategoryTheory.Equivalence.mk (toSpacesEtale R) (ofSpacesEtale R) (unitIso R) (counitIso R)

/-- The forward comparison is pullback to the reduction. -/
@[simp]
theorem spacesEtaleEquiv_functor : (spacesEtaleEquiv R).functor = toSpacesEtale R := rfl

/-- The inverse comparison is extension of commuting pairs along the reduction. -/
@[simp]
theorem spacesEtaleEquiv_inverse : (spacesEtaleEquiv R).inverse = ofSpacesEtale R := rfl

end AlgebraicGeometry.FormalAlgebraicSpace.ReductionData
