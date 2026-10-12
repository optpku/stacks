/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.Limits.Over.Products
public import stacks_project.Chap65.Definition_65_9_3_Presentation
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Change of base scheme for algebraic spaces

A morphism `g : S ⟶ S'` induces the localization functor `j = Over.map g` on slice
categories of schemes. This module records the Type `u` functor-of-points transport of
algebraic spaces along `j`: the explicit coproduct formula for `j_!`, restriction
`j⁻¹`, and the induced maps on pre-relations and presentations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- View a pre-relation on `U` over `S` as a pre-relation on `U` over `S'` along `g : S ⟶ S'`,
by applying `Over.map g` and composing with the comparison `(U ⨯_S U) ⟶ (j U ⨯_{S'} j U)`. -/
def viewedOver {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S} (P : PreRelation U) :
    PreRelation ((Over.map g).obj U) :=
  ofHom ((Over.map g).map P.hom ≫ prodComparison (Over.map g) U U)

/-- The source of `viewedOver g P` is `P` viewed as a scheme over `S'`. -/
@[simp]
theorem viewedOver_left {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S}
    (P : PreRelation U) :
    (P.viewedOver g).left = (Over.map g).obj P.left := sorry

/-- The first projection of `viewedOver g P` is the image of `P.t` under `Over.map g`. -/
@[simp]
theorem viewedOver_t {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S} (P : PreRelation U) :
    (P.viewedOver g).t = (Over.map g).map P.t := sorry

/-- The second projection of `viewedOver g P` is the image of `P.s` under `Over.map g`. -/
@[simp]
theorem viewedOver_s {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S} (P : PreRelation U) :
    (P.viewedOver g).s = (Over.map g).map P.s := sorry

/-- The underlying scheme morphism of the first projection of `viewedOver g P` agrees with
that of `P.t`. -/
theorem viewedOver_t_left {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S}
    (P : PreRelation U) :
    (P.viewedOver g).t.left = P.t.left := sorry

/-- The underlying scheme morphism of the second projection of `viewedOver g P` agrees with
that of `P.s`. -/
theorem viewedOver_s_left {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S}
    (P : PreRelation U) :
    (P.viewedOver g).s.left = P.s.left := sorry

/-- Base change a pre-relation on `U'` over `S'` to a pre-relation on `U'_S` over `S`, by
applying `Over.pullback g` and the product comparison. -/
def baseChange {S S' : Scheme.{u}} (g : S ⟶ S') {U' : Over S'} (P : PreRelation U') :
    PreRelation ((Over.pullback g).obj U') :=
  ofHom ((Over.pullback g).map P.hom ≫ prodComparison (Over.pullback g) U' U')

/-- The source of `baseChange g P` is the pullback of the source of `P` along `g`. -/
@[simp]
theorem baseChange_left {S S' : Scheme.{u}} (g : S ⟶ S') {U' : Over S'}
    (P : PreRelation U') :
    (P.baseChange g).left = (Over.pullback g).obj P.left := sorry

/-- The first projection of `baseChange g P` is the image of `P.t` under `Over.pullback g`. -/
@[simp]
theorem baseChange_t {S S' : Scheme.{u}} (g : S ⟶ S') {U' : Over S'}
    (P : PreRelation U') :
    (P.baseChange g).t = (Over.pullback g).map P.t := sorry

/-- The second projection of `baseChange g P` is the image of `P.s` under `Over.pullback g`. -/
@[simp]
theorem baseChange_s {S S' : Scheme.{u}} (g : S ⟶ S') {U' : Over S'}
    (P : PreRelation U') :
    (P.baseChange g).s = (Over.pullback g).map P.s := sorry

end AlgebraicGeometry.Scheme.PreRelation

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism in `Over S` induced by a morphism of schemes over `S'` after postcomposing
the structure map to `S`. -/
def restrictIndex {S S' : Scheme.{u}} {T' T'' : Over S'} {g : S ⟶ S'}
    (f : T'' ⟶ T') (φ : T' ⟶ Over.mk g) :
    Over.mk (f ≫ φ).left ⟶ Over.mk φ.left :=
  Over.homMk f.left

/-- The first projection of `restrictIndex f φ` is `f`. -/
@[simp]
theorem restrictIndex_left {S S' : Scheme.{u}} {T' T'' : Over S'} {g : S ⟶ S'}
    (f : T'' ⟶ T') (φ : T' ⟶ Over.mk g) :
    (restrictIndex f φ).left = f.left := sorry

/-- The coproduct formula for `j_!` on `Type u`-valued presheaves: a section over `T'` over
`S'` is a morphism `φ : T' ⟶ S` over `S'` together with a section of `F` over `T'` viewed
over `S` via `φ`. -/
def extendBasePresheaf {S S' : Scheme.{u}} (g : S ⟶ S') (F : (Over S)ᵒᵖ ⥤ Type u) :
    (Over S')ᵒᵖ ⥤ Type u where
  obj T' := Σ φ : T'.unop ⟶ Over.mk g, F.obj (op (Over.mk φ.left))
  map {T' T''} f := ofHom fun σ ↦
    ⟨f.unop ≫ σ.1, F.map (restrictIndex f.unop σ.1).op σ.2⟩
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- Evaluating `extendBasePresheaf g F` on `T'` is the coproduct of the values of `F` over
morphisms `T' ⟶ Over.mk g`. -/
theorem extendBasePresheaf_map_apply {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : (Over S)ᵒᵖ ⥤ Type u) {T' T'' : Over S'} (f : T'' ⟶ T')
    (φ : T' ⟶ Over.mk g) (s : F.obj (op (Over.mk φ.left))) :
    (extendBasePresheaf g F).map f.op ⟨φ, s⟩ =
      ⟨f ≫ φ, F.map (restrictIndex f φ).op s⟩ := sorry

/-- A morphism of presheaves over `S` induces a morphism of their `j_!` coproduct
presheaves over `S'`. -/
def extendBasePresheafMap {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} (α : F ⟶ G) :
    extendBasePresheaf g F ⟶ extendBasePresheaf g G where
  app T' := ofHom fun σ ↦ ⟨σ.1, α.app (op (Over.mk σ.1.left)) σ.2⟩
  naturality := fun _ _ _ ↦ sorry

/-- Applying `extendBasePresheafMap` keeps the index and applies `α` on the corresponding
summand. -/
theorem extendBasePresheafMap_apply {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} (α : F ⟶ G) {T' : Over S'}
    (φ : T' ⟶ Over.mk g) (s : F.obj (op (Over.mk φ.left))) :
    (extendBasePresheafMap g α).app (op T') ⟨φ, s⟩ =
      ⟨φ, α.app (op (Over.mk φ.left)) s⟩ := sorry

/-- The triangle identity for a slice map into `X` after viewing `X` over `S'` along `g`. -/
theorem homMk_viewedOver_w {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S}
    {T' : Over S'} {φ : T' ⟶ Over.mk g} (β : Over.mk φ.left ⟶ X) :
    β.left ≫ ((Over.map g).obj X).hom = T'.hom := sorry

/-- The structure map to `S` of a morphism into `X` viewed over `S'` is a morphism
`T' ⟶ Over.mk g`. -/
theorem homMk_index_w {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (α : T' ⟶ (Over.map g).obj X) :
    (α.left ≫ X.hom) ≫ g = T'.hom := sorry

/-- Assemble a morphism `T' ⟶ j(X)` from an index `φ : T' ⟶ S` over `S'` and a morphism
over `S` into `X`. -/
def homOfIndex {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (φ : T' ⟶ Over.mk g) (β : Over.mk φ.left ⟶ X) :
    T' ⟶ (Over.map g).obj X :=
  Over.homMk β.left (homMk_viewedOver_w g β)

/-- The underlying scheme morphism of `homOfIndex g φ β` is `β.left`. -/
@[simp]
theorem homOfIndex_left {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (φ : T' ⟶ Over.mk g) (β : Over.mk φ.left ⟶ X) :
    (homOfIndex g φ β).left = β.left := sorry

/-- The index `T' ⟶ Over.mk g` associated to a morphism `T' ⟶ j(X)`. -/
def indexOfHom {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (α : T' ⟶ (Over.map g).obj X) : T' ⟶ Over.mk g :=
  Over.homMk (α.left ≫ X.hom) (homMk_index_w g α)

/-- The underlying scheme morphism of `indexOfHom g α` is `α.left ≫ X.hom`. -/
@[simp]
theorem indexOfHom_left {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (α : T' ⟶ (Over.map g).obj X) :
    (indexOfHom g α).left = α.left ≫ X.hom := sorry

/-- The morphism over `S` into `X` associated to a morphism `T' ⟶ j(X)`. -/
def homOverOfHom {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (α : T' ⟶ (Over.map g).obj X) :
    Over.mk (indexOfHom g α).left ⟶ X :=
  Over.homMk α.left

/-- The underlying scheme morphism of `homOverOfHom g α` is `α.left`. -/
@[simp]
theorem homOverOfHom_left {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (α : T' ⟶ (Over.map g).obj X) :
    (homOverOfHom g α).left = α.left := sorry

/-- The coproduct formula for `j_!` of a representable presheaf is the representable
presheaf of `j(X)`. -/
def extendBasePresheafYonedaIso {S S' : Scheme.{u}} (g : S ⟶ S') (X : Over S) :
    extendBasePresheaf g (yoneda.obj X) ≅ yoneda.obj ((Over.map g).obj X) where
  hom :=
    { app := fun T' ↦ ofHom fun σ ↦ homOfIndex g σ.1 σ.2
      naturality := fun _ _ _ ↦ sorry }
  inv :=
    { app := fun T' ↦ ofHom fun α ↦ ⟨indexOfHom g α, homOverOfHom g α⟩
      naturality := fun _ _ _ ↦ sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `extendBasePresheafYonedaIso` packages an index and a slice morphism
into a morphism over `S'`. -/
theorem extendBasePresheafYonedaIso_hom_apply {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : Over S) {T' : Over S'} (φ : T' ⟶ Over.mk g) (β : Over.mk φ.left ⟶ X) :
    (extendBasePresheafYonedaIso g X).hom.app (op T') ⟨φ, β⟩ = homOfIndex g φ β := sorry

/-- The inverse map of `extendBasePresheafYonedaIso` splits a morphism over `S'` into its
index and its morphism over `S`. -/
theorem extendBasePresheafYonedaIso_inv_apply {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : Over S) {T' : Over S'} (α : T' ⟶ (Over.map g).obj X) :
    (extendBasePresheafYonedaIso g X).inv.app (op T') α =
      ⟨indexOfHom g α, homOverOfHom g α⟩ := sorry

/-- If `F` is an fppf sheaf on `Over S`, then `extendBasePresheaf g F` is an fppf sheaf on
`Over S'`. -/
theorem isSheaf_extendBasePresheaf {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : (Over S)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S') (extendBasePresheaf g F) := sorry

/-- View an algebraic space over `S` as an algebraic space over `S'` along `g`, using the
explicit coproduct formula for `j_!` on functors of points. -/
def extendBase {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    AlgebraicSpace S' :=
  ofFunctor (extendBasePresheaf g F.functorOfPoints) sorry sorry sorry

/-- The functor of points of `extendBase g F` is the coproduct presheaf `extendBasePresheaf`. -/
@[simp]
theorem extendBase_functorOfPoints {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S) :
    (extendBase g F).functorOfPoints = extendBasePresheaf g F.functorOfPoints := sorry

/-- Restriction of presheaves along `j = Over.map g` is precomposition with `(Over.map g).op`. -/
abbrev baseChangePresheaf {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) : (Over S)ᵒᵖ ⥤ Type u :=
  (Over.map g).op ⋙ F'

/-- Evaluating `baseChangePresheaf g F'` on a morphism over `S` is evaluation of `F'` after
applying `Over.map g`. -/
theorem baseChangePresheaf_app {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) {T T' : Over S} (f : T ⟶ T') :
    (baseChangePresheaf g F').map f.op = F'.map ((Over.map g).map f).op := sorry

/-- The inverse image of a representable presheaf along `j = Over.map g` is the representable
presheaf of the chosen pullback `S ×_{S'} X'`. -/
def baseChangePresheafYonedaIso {S S' : Scheme.{u}} (g : S ⟶ S') (X' : Over S') :
    baseChangePresheaf g (yoneda.obj X') ≅ yoneda.obj ((Over.pullback g).obj X') :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso ((Over.mapPullbackAdj g).homEquiv T.unop X')) sorry

/-- The forward map of `baseChangePresheafYonedaIso` is the adjunction equivalence
`Over.map g ⊣ Over.pullback g`. -/
theorem baseChangePresheafYonedaIso_hom_apply {S S' : Scheme.{u}} (g : S ⟶ S')
    (X' : Over S') {T : Over S} (α : (Over.map g).obj T ⟶ X') :
    (baseChangePresheafYonedaIso g X').hom.app (op T) α =
      (Over.mapPullbackAdj g).homEquiv T X' α := sorry

/-- Base change an algebraic space over `S'` to an algebraic space over `S` along `g`, by
restricting the functor of points along `Over.map g`. -/
def baseChange {S S' : Scheme.{u}} (g : S ⟶ S') (F' : AlgebraicSpace S') :
    AlgebraicSpace S :=
  ofFunctor (baseChangePresheaf g F'.functorOfPoints) sorry sorry sorry

/-- The functor of points of `baseChange g F'` is restriction of the functor of points of
`F'` along `Over.map g`. -/
@[simp]
theorem baseChange_functorOfPoints {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : AlgebraicSpace S') :
    (baseChange g F').functorOfPoints = baseChangePresheaf g F'.functorOfPoints := sorry

/-- If `F'` is an fppf sheaf on `Over S'`, then `baseChangePresheaf g F'` is an fppf sheaf on
`Over S`. -/
theorem isSheaf_baseChangePresheaf {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u)
    (hF' : Presheaf.IsSheaf (Scheme.fppfTopology.over S') F') :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (baseChangePresheaf g F') := sorry

/-- The inverse image of a sheaf along `j = Over.map g` evaluates by applying `Over.map g` to
the slice object. -/
theorem overMapPullback_obj_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : Sheaf (Scheme.fppfTopology.over S') (Type u)) (T : Over S) :
    ((Scheme.fppfTopology.overMapPullback (Type u) g).obj F').obj.obj (op T) =
      F'.obj.obj (op ((Over.map g).obj T)) := sorry

/-- Viewing the representable algebraic space of `X` over `S` along `g` recovers the
representable algebraic space of `j(X)`. -/
def extendBase_ofOver_functorOfPoints {S S' : Scheme.{u}} (g : S ⟶ S') (X : Over S) :
    (extendBase g (ofOver X)).functorOfPoints ≅
      (ofOver ((Over.map g).obj X)).functorOfPoints :=
  extendBasePresheafYonedaIso g X

/-- The algebraic-space identification for representables is the coproduct-to-yoneda
comparison. -/
theorem extendBase_ofOver_functorOfPoints_eq {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : Over S) :
    extendBase_ofOver_functorOfPoints g X = extendBasePresheafYonedaIso g X := sorry

/-- Base changing the representable algebraic space of `X'` along `g` recovers the
representable algebraic space of `S ×_{S'} X'`. -/
def baseChange_ofOver_functorOfPoints {S S' : Scheme.{u}} (g : S ⟶ S')
    (X' : Over S') :
    (baseChange g (ofOver X')).functorOfPoints ≅
      (ofOver ((Over.pullback g).obj X')).functorOfPoints :=
  baseChangePresheafYonedaIso g X'

/-- The algebraic-space identification for inverse images of representables is the
adjunction comparison. -/
theorem baseChange_ofOver_functorOfPoints_eq {S S' : Scheme.{u}} (g : S ⟶ S')
    (X' : Over S') :
    baseChange_ofOver_functorOfPoints g X' = baseChangePresheafYonedaIso g X' := sorry

namespace Presentation

/-- Transport a presentation along `j = Over.map g`: the scheme, relation, and atlas are
viewed over `S'`. -/
def extendBase {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S')
    (P : Presentation F) : Presentation (AlgebraicSpace.extendBase g F) where
  U := (Over.map g).obj P.U
  R := P.R.viewedOver g
  atlas := (extendBasePresheafYonedaIso g P.U).inv ≫ extendBasePresheafMap g P.atlas
  isEtaleEquivalence := sorry
  atlas_etale := sorry
  atlas_locallySurjective := sorry
  isKernelPair := sorry

/-- The presenting scheme of `Presentation.extendBase g P` is `j(P.U)`. -/
@[simp]
theorem extendBase_U {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S')
    (P : Presentation F) :
    (P.extendBase g).U = (Over.map g).obj P.U := sorry

/-- The relation of `Presentation.extendBase g P` is `j(P.R)`. -/
@[simp]
theorem extendBase_R {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S')
    (P : Presentation F) :
    (P.extendBase g).R = P.R.viewedOver g := sorry

/-- The atlas of `Presentation.extendBase g P` is the transport of `P.atlas` along the
representable identification `h_{j(U)} ≅ j_! h_U`. -/
theorem extendBase_atlas {S S' : Scheme.{u}} {F : AlgebraicSpace S} (g : S ⟶ S')
    (P : Presentation F) :
    (P.extendBase g).atlas =
      (extendBasePresheafYonedaIso g P.U).inv ≫ extendBasePresheafMap g P.atlas := sorry

/-- Transport a presentation along `j⁻¹`: the scheme and relation are pulled back to `S`. -/
def baseChange {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S')
    (P : Presentation F') : Presentation (AlgebraicSpace.baseChange g F') where
  U := (Over.pullback g).obj P.U
  R := P.R.baseChange g
  atlas := (baseChangePresheafYonedaIso g P.U).inv ≫
    Functor.whiskerLeft (Over.map g).op P.atlas
  isEtaleEquivalence := sorry
  atlas_etale := sorry
  atlas_locallySurjective := sorry
  isKernelPair := sorry

/-- The presenting scheme of `Presentation.baseChange g P` is `P.U` pulled back to `S`. -/
@[simp]
theorem baseChange_U {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S')
    (P : Presentation F') :
    (P.baseChange g).U = (Over.pullback g).obj P.U := sorry

/-- The relation of `Presentation.baseChange g P` is `P.R` pulled back to `S`. -/
@[simp]
theorem baseChange_R {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S')
    (P : Presentation F') :
    (P.baseChange g).R = P.R.baseChange g := sorry

/-- The atlas of `Presentation.baseChange g P` is the restriction of `P.atlas` along
`Over.map g`, transported by the representable identification. -/
theorem baseChange_atlas {S S' : Scheme.{u}} {F' : AlgebraicSpace S'} (g : S ⟶ S')
    (P : Presentation F') :
    (P.baseChange g).atlas =
      (baseChangePresheafYonedaIso g P.U).inv ≫ Functor.whiskerLeft (Over.map g).op P.atlas := sorry

end Presentation

end AlgebraicGeometry.AlgebraicSpace
