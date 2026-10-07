module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Equivalence
public import stacks_project.Chap78.Lemma_78_21_1_QuotientMap
public import stacks_project.Chap78.Lemma_78_22_2_Square
public import stacks_project.Chap83.Lemma_83_3_3_Groupoid

/-!
# 2-fibre product square of a base-changed quotient stack

An `R`-invariant morphism `φ : U ⟶ X` lets a groupoid in algebraic spaces over `B` be
regarded over `X`. Base change along `g : X' ⟶ X` produces `(U', R')` over `X'`. After
transport to a common base, the induced maps of quotient stacks and stacks in sets pack into
a pseudopullback cone with apex `[U'/R']` on the cospan `[U/R] ⟶ 𝒮_X ← 𝒮_{X'}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits Opposite
open CategoryTheory.Bicategory CategoryTheory.CategoryOfElements
open Functor.IsFibered.InGroupoids.Stackification
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The groupoid `(U, R, s, t, c)` regarded over `X` along an invariant morphism `φ`. -/
abbrev overX {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    GroupoidAlgebraicSpace X.left :=
  over G φ hφ

/-- The base change `(U', R', s', t', c')` of `overX` along `g.left : X'.left ⟶ X.left`. -/
abbrev baseChangeOver {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X X' : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    GroupoidAlgebraicSpace X'.left :=
  baseChange g.left (overX G φ hφ)

/-- The base-changed groupoid viewed over `X`, so that `Hom` with `overX` is well-typed. -/
abbrev transportedBaseChange {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    GroupoidAlgebraicSpace X.left :=
  changeBase g.left (baseChangeOver G φ hφ g)

/-- The morphism of groupoids over `X` whose object and arrow maps are the counit projections
`U' ⟶ U` and `R' ⟶ R`. -/
def baseChangeHom {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X X' : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    Hom (transportedBaseChange G φ hφ g) (overX G φ hφ) where
  obj := baseChangeCounit g.left (overX G φ hφ).U
  arrow := baseChangeCounit g.left (overX G φ hφ).R
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of `baseChangeHom` is the counit projection of `U'`. -/
theorem baseChangeHom_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeHom G φ hφ g).obj = baseChangeCounit g.left (overX G φ hφ).U := sorry

/-- The arrow component of `baseChangeHom` is the counit projection of `R'`. -/
theorem baseChangeHom_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeHom G φ hφ g).arrow = baseChangeCounit g.left (overX G φ hφ).R := sorry

/-- Fibre compatibility for a co-Grothendieck arrow after postcomposition by `h`. -/
theorem prestackToSpace_map_w {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B')
    {x y : (prestack G).total} (f : x ⟶ y) :
    B'.functorOfPoints.map f.base.op (yonedaEquiv (y.fiber ≫ h)) =
      yonedaEquiv (x.fiber ≫ h) := sorry

/-- The total functor `[U/_p R] ⟶ 𝒮_{B'}` sending a point of `U` to its image under `h`. -/
def prestackToSpaceFunctor {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') :
    (prestack G).total ⥤ (stackInSets B').total where
  obj x := op ⟨op x.base, yonedaEquiv (x.fiber ≫ h)⟩
  map {x y} f :=
    (homMk ⟨op y.base, yonedaEquiv (y.fiber ≫ h)⟩
        ⟨op x.base, yonedaEquiv (x.fiber ≫ h)⟩ f.base.op
        (prestackToSpace_map_w G h f)).op
  map_id := sorry
  map_comp := sorry

/-- Compatibility of `prestackToSpaceFunctor` with the projections. -/
theorem prestackToSpace_w {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') :
    prestackToSpaceFunctor G h ⋙ (stackInSets B').p = (prestack G).p := sorry

/-- The cartesian `1`-morphism `[U/_p R] ⟶ 𝒮_{B'}` induced by a morphism `U ⟶ B'`. -/
def prestackToSpace {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') :
    CartesianBasedFunctor (prestack G).p (stackInSets B').p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (prestackToSpaceFunctor G h) (prestackToSpace_w G h))

/-- The selected stackification lift of `prestackToSpace` through `[U/_p R] ⟶ [U/R]`. -/
def fppfToSpaceLift {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation G).comparison) (prestackToSpace G h) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (fppfQuotientStackPresentation G).isStackification (prestackToSpace G h)

/-- The cartesian `1`-morphism `[U/R] ⟶ 𝒮_{B'}` obtained by lifting `prestackToSpace`. -/
def fppfToSpace {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') :
    CartesianBasedFunctor (fppfQuotientStack G).p (stackInSets B').p :=
  (fppfToSpaceLift G h).lift

/-- The cartesian `1`-morphism `[U/R] ⟶ 𝒮_B` of Lemma 78.20.2, on the fppf quotient stack. -/
def fppfToBase {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (fppfQuotientStack G).p (stackInSets B).p :=
  fppfToSpace G G.U.hom

/-- The cartesian `1`-morphism `[U/R] ⟶ 𝒮_B` after aligning Hom-universes. -/
def toSpaceHomCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (fppfQuotientStack G).p (stackInSetsULift B).p :=
  (fppfToBase G).comp (stackInSetsULift.up B)

/-- The `1`-morphism `[U/R] ⟶ 𝒮_B` of stacks in groupoids over `(Sch/S)_fppf`. -/
def toSpaceHom {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    fppfQuotientStack G ⟶ stackInSetsULift B :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (toSpaceHomCartesian G).toBasedFunctor)

/-- `toSpaceHom G` is the universe-aligned lift of `fppfToBase G`. -/
theorem toSpaceHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    StackOver.Groupoids.Hom.toCartesianBasedFunctor (toSpaceHom G) =
      toSpaceHomCartesian G := sorry

/-- The cartesian top arrow `[U'/R'] ⟶ [U/R]` induced by `baseChangeHom`. -/
def baseChangeQuotientMapCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    CartesianBasedFunctor (fppfQuotientStack (transportedBaseChange G φ hφ g)).p
      (fppfQuotientStack (overX G φ hφ)).p :=
  Hom.quotientStackMap (baseChangeHom G φ hφ g)

/-- The top arrow `[U'/R'] ⟶ [U/R]` as a morphism of stacks in groupoids. -/
def baseChangeQuotientMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    fppfQuotientStack (transportedBaseChange G φ hφ g) ⟶
      fppfQuotientStack (overX G φ hφ) :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (baseChangeQuotientMapCartesian G φ hφ g).toBasedFunctor)

/-- The cartesian left arrow `[U'/R'] ⟶ 𝒮_{X'}` induced by the structure morphism of `U'`
over `X'`, on the transported quotient stack. -/
def baseChangeToSpaceHomCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    CartesianBasedFunctor (fppfQuotientStack (transportedBaseChange G φ hφ g)).p
      (stackInSetsULift X'.left).p :=
  (fppfToSpace (transportedBaseChange G φ hφ g) (baseChangeOver G φ hφ g).U.hom).comp
    (stackInSetsULift.up X'.left)

/-- The left arrow `[U'/R'] ⟶ 𝒮_{X'}` as a morphism of stacks in groupoids. -/
def baseChangeToSpaceHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    fppfQuotientStack (transportedBaseChange G φ hφ g) ⟶ stackInSetsULift X'.left :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (baseChangeToSpaceHomCartesian G φ hφ g).toBasedFunctor)

/-- The cartesian bottom arrow `𝒮_{X'} ⟶ 𝒮_X` induced by `g`. -/
def baseChangeSpaceMapCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    {X X' : Over B} (g : X' ⟶ X) :
    CartesianBasedFunctor (stackInSetsULift X'.left).p (stackInSetsULift X.left).p :=
  ((stackInSetsULift.down X'.left).comp (stackInSets.map g.left)).comp
    (stackInSetsULift.up X.left)

/-- The prestack morphism `[U'/_p R'] ⟶ 𝒮_X` along the composite `U' ⟶ X' ⟶ X`. -/
def baseChangePrestackToSpace {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    CartesianBasedFunctor (prestack (transportedBaseChange G φ hφ g)).p
      (stackInSets X.left).p :=
  prestackToSpace (transportedBaseChange G φ hφ g)
    ((baseChangeOver G φ hφ g).U.hom ≫ g.left)

/-- The prestack morphism `[U'/_p R'] ⟶ 𝒮_X` along the composite `U' ⟶ U ⟶ X`. -/
def baseChangePrestackToSpaceViaCounit {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    CartesianBasedFunctor (prestack (transportedBaseChange G φ hφ g)).p
      (stackInSets X.left).p :=
  prestackToSpace (transportedBaseChange G φ hφ g)
    ((baseChangeHom G φ hφ g).obj.left ≫ (overX G φ hφ).U.hom)

/-- Objectwise, the explicit `yonedaEquiv` formulas for counit-then-`φ` and `U'.hom`-then-`g`
agree. -/
theorem baseChangePrestackToSpace_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X)
    (x : (prestack (transportedBaseChange G φ hφ g)).total) :
    (baseChangePrestackToSpaceViaCounit G φ hφ g).toFunctor.obj x =
      (baseChangePrestackToSpace G φ hφ g).toFunctor.obj x := sorry

/-- Objectwise, postcomposing the counit of `U'` then `φ` agrees with `prestackMap` then
`prestackToSpace` of `overX`. -/
theorem baseChangePrestackMap_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X)
    (x : (prestack (transportedBaseChange G φ hφ g)).total) :
    ((Hom.prestackMap (baseChangeHom G φ hφ g)).comp
          (prestackToSpace (overX G φ hφ) (overX G φ hφ).U.hom)).toFunctor.obj x =
      (baseChangePrestackToSpaceViaCounit G φ hφ g).toFunctor.obj x := sorry

/-- Objectwise, `prestackToSpace` along `U' ⟶ X'` then `𝒮_{X'} ⟶ 𝒮_X` agrees with the composite
`U' ⟶ X`. -/
theorem baseChangePrestackSpaceMap_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X)
    (x : (prestack (transportedBaseChange G φ hφ g)).total) :
    ((prestackToSpace (transportedBaseChange G φ hφ g)
            (baseChangeOver G φ hφ g).U.hom).comp
          (stackInSets.map g.left)).toFunctor.obj x =
      (baseChangePrestackToSpace G φ hφ g).toFunctor.obj x := sorry

/-- The cartesian identification of the two explicit prestack maps `[U'/_p R'] ⟶ 𝒮_X`. -/
def baseChangePrestackToSpaceIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    baseChangePrestackToSpaceViaCounit G φ hφ g ≅
      baseChangePrestackToSpace G φ hφ g where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ eqToHom (baseChangePrestackToSpace_obj G φ hφ g x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ eqToHom (baseChangePrestackToSpace_obj G φ hφ g x).symm
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The cartesian identification of `prestackMap` then `prestackToSpace` with counit-then-`φ`. -/
def baseChangePrestackMapIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (Hom.prestackMap (baseChangeHom G φ hφ g)).comp
        (prestackToSpace (overX G φ hφ) (overX G φ hφ).U.hom) ≅
      baseChangePrestackToSpaceViaCounit G φ hφ g where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ eqToHom (baseChangePrestackMap_obj G φ hφ g x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ eqToHom (baseChangePrestackMap_obj G φ hφ g x).symm
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The cartesian identification of `prestackToSpace` along `U' ⟶ X'` then `𝒮`-pushforward with
the composite `U' ⟶ X`. -/
def baseChangePrestackSpaceMapIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (prestackToSpace (transportedBaseChange G φ hφ g)
          (baseChangeOver G φ hφ g).U.hom).comp
        (stackInSets.map g.left) ≅
      baseChangePrestackToSpace G φ hφ g where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ eqToHom (baseChangePrestackSpaceMap_obj G φ hφ g x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ eqToHom (baseChangePrestackSpaceMap_obj G φ hφ g x).symm
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-objects associator identifying `((i ≫ [f]) ≫ toSpace)` with
`i ≫ ([f] ≫ toSpace)`. -/
def baseChangeQuotientLeftAssoc {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    ((fppfQuotientStackPresentation (transportedBaseChange G φ hφ g)).comparison.comp
          (Hom.quotientStackMap (baseChangeHom G φ hφ g))).comp
        (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom) ≅
      (fppfQuotientStackPresentation (transportedBaseChange G φ hφ g)).comparison.comp
        ((Hom.quotientStackMap (baseChangeHom G φ hφ g)).comp
          (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          𝟙 ((((fppfQuotientStackPresentation
                  (transportedBaseChange G φ hφ g)).comparison.comp
                (Hom.quotientStackMap (baseChangeHom G φ hφ g))).comp
              (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          𝟙 ((((fppfQuotientStackPresentation
                  (transportedBaseChange G φ hφ g)).comparison.comp
                (Hom.quotientStackMap (baseChangeHom G φ hφ g))).comp
              (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-objects associator identifying `(prestackToQuotient ≫ toSpace)` with
`prestackMap ≫ (i ≫ toSpace)`. -/
def baseChangeQuotientLeftPreAssoc {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (Hom.prestackToQuotient (baseChangeHom G φ hφ g)).comp
        (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom) ≅
      (Hom.prestackMap (baseChangeHom G φ hφ g)).comp
        ((fppfQuotientStackPresentation (overX G φ hφ)).comparison.comp
          (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          𝟙 (((Hom.prestackToQuotient (baseChangeHom G φ hφ g)).comp
              (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          𝟙 (((Hom.prestackToQuotient (baseChangeHom G φ hφ g)).comp
              (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-objects associator identifying `((i ≫ toSpace_{X'}) ≫ 𝒮_g)` with
`i ≫ (toSpace_{X'} ≫ 𝒮_g)`. -/
def baseChangeQuotientRightAssoc {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    ((fppfQuotientStackPresentation (transportedBaseChange G φ hφ g)).comparison.comp
          (fppfToSpace (transportedBaseChange G φ hφ g)
            (baseChangeOver G φ hφ g).U.hom)).comp
        (stackInSets.map g.left) ≅
      (fppfQuotientStackPresentation (transportedBaseChange G φ hφ g)).comparison.comp
        ((fppfToSpace (transportedBaseChange G φ hφ g)
            (baseChangeOver G φ hφ g).U.hom).comp (stackInSets.map g.left)) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          𝟙 ((((fppfQuotientStackPresentation
                  (transportedBaseChange G φ hφ g)).comparison.comp
                (fppfToSpace (transportedBaseChange G φ hφ g)
                  (baseChangeOver G φ hφ g).U.hom)).comp
              (stackInSets.map g.left)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          𝟙 ((((fppfQuotientStackPresentation
                  (transportedBaseChange G φ hφ g)).comparison.comp
                (fppfToSpace (transportedBaseChange G φ hφ g)
                  (baseChangeOver G φ hφ g).U.hom)).comp
              (stackInSets.map g.left)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The stackification lift of the prestack map along `U' ⟶ X` whose lift is
`[f] ≫ ([U/R] ⟶ 𝒮_X)`. -/
def baseChangeQuotientLeftLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (transportedBaseChange G φ hφ g)).comparison)
      (baseChangePrestackToSpace G φ hφ g) where
  lift :=
    (Hom.quotientStackMap (baseChangeHom G φ hφ g)).comp
      (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)
  comparison :=
    (baseChangeQuotientLeftAssoc G φ hφ g).symm ≪≫
      (CartesianBasedFunctor.postcomp
          (prestack (transportedBaseChange G φ hφ g)).p
          (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)).mapIso
        (Hom.quotientStackMap_comp (baseChangeHom G φ hφ g)) ≪≫
      baseChangeQuotientLeftPreAssoc G φ hφ g ≪≫
      (CartesianBasedFunctor.precomp (stackInSets X.left).p
          (Hom.prestackMap (baseChangeHom G φ hφ g))).mapIso
        (fppfToSpaceLift (overX G φ hφ) (overX G φ hφ).U.hom).comparison ≪≫
      baseChangePrestackMapIso G φ hφ g ≪≫
      baseChangePrestackToSpaceIso G φ hφ g

/-- The stackification lift of the prestack map along `U' ⟶ X` whose lift is
`([U'/R'] ⟶ 𝒮_{X'}) ≫ 𝒮_g`. -/
def baseChangeQuotientRightLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (transportedBaseChange G φ hφ g)).comparison)
      (baseChangePrestackToSpace G φ hφ g) where
  lift :=
    (fppfToSpace (transportedBaseChange G φ hφ g)
        (baseChangeOver G φ hφ g).U.hom).comp (stackInSets.map g.left)
  comparison :=
    (baseChangeQuotientRightAssoc G φ hφ g).symm ≪≫
      (CartesianBasedFunctor.postcomp
          (prestack (transportedBaseChange G φ hφ g)).p
          (stackInSets.map g.left)).mapIso
        (fppfToSpaceLift (transportedBaseChange G φ hφ g)
          (baseChangeOver G φ hφ g).U.hom).comparison ≪≫
      baseChangePrestackSpaceMapIso G φ hφ g

/-- The unlifted cartesian `2`-isomorphism of `[f] ≫ ([U/R] ⟶ 𝒮_X)` with
`([U'/R'] ⟶ 𝒮_{X'}) ≫ 𝒮_g`. -/
def baseChangeQuotientUnliftedIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (Hom.quotientStackMap (baseChangeHom G φ hφ g)).comp
        (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom) ≅
      (fppfToSpace (transportedBaseChange G φ hφ g)
          (baseChangeOver G φ hφ g).U.hom).comp (stackInSets.map g.left) :=
  CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso
    (fppfQuotientStackPresentation (transportedBaseChange G φ hφ g)).isStackification
    (baseChangeQuotientLeftLift G φ hφ g) (baseChangeQuotientRightLift G φ hφ g)

/-- Identity-on-objects associator identifying `([f] ≫ toSpace) ≫ up` with
`[f] ≫ (toSpace ≫ up)`. -/
def baseChangeQuotientIsoLeftAssoc {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    ((Hom.quotientStackMap (baseChangeHom G φ hφ g)).comp
          (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)).comp
        (stackInSetsULift.up X.left) ≅
      (Hom.quotientStackMap (baseChangeHom G φ hφ g)).comp
        ((fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom).comp
          (stackInSetsULift.up X.left)) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          𝟙 ((((Hom.quotientStackMap (baseChangeHom G φ hφ g)).comp
                (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)).comp
              (stackInSetsULift.up X.left)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          𝟙 ((((Hom.quotientStackMap (baseChangeHom G φ hφ g)).comp
                (fppfToSpace (overX G φ hφ) (overX G φ hφ).U.hom)).comp
              (stackInSetsULift.up X.left)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Comparison identifying the unlifted composite after `up` with the universe-aligned
cospan composite, using the unit of the two-universe equivalence of `𝒮_{X'}`. -/
def baseChangeQuotientIsoRightAlign {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    ((fppfToSpace (transportedBaseChange G φ hφ g)
            (baseChangeOver G φ hφ g).U.hom).comp
          (stackInSets.map g.left)).comp (stackInSetsULift.up X.left) ≅
      (baseChangeToSpaceHomCartesian G φ hφ g).comp (baseChangeSpaceMapCartesian g) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          ((stackInSets.map g.left).comp (stackInSetsULift.up X.left)).toFunctor.map
            ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
                (stackInSets X'.left).total).unitIso.hom.app
              ((fppfToSpace (transportedBaseChange G φ hφ g)
                  (baseChangeOver G φ hφ g).U.hom).toFunctor.obj x))
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          ((stackInSets.map g.left).comp (stackInSetsULift.up X.left)).toFunctor.map
            ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
                (stackInSets X'.left).total).unitIso.inv.app
              ((fppfToSpace (transportedBaseChange G φ hφ g)
                  (baseChangeOver G φ hφ g).U.hom).toFunctor.obj x))
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The cartesian `2`-isomorphism of the two composites `[U'/R'] ⟶ 𝒮_X`. -/
def baseChangeQuotientIsoCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientMapCartesian G φ hφ g).comp
        (toSpaceHomCartesian (overX G φ hφ)) ≅
      (baseChangeToSpaceHomCartesian G φ hφ g).comp (baseChangeSpaceMapCartesian g) :=
  (baseChangeQuotientIsoLeftAssoc G φ hφ g).symm ≪≫
    (CartesianBasedFunctor.postcomp
        (fppfQuotientStack (transportedBaseChange G φ hφ g)).p
        (stackInSetsULift.up X.left)).mapIso
      (baseChangeQuotientUnliftedIso G φ hφ g) ≪≫
    baseChangeQuotientIsoRightAlign G φ hφ g

/-- The invertible `2`-cell of the source square, oriented `fst ≫ right ≅ snd ≫ bottom`. -/
def baseChangeQuotientIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    baseChangeQuotientMap G φ hφ g ≫ toSpaceHom (overX G φ hφ) ≅
      baseChangeToSpaceHom G φ hφ g ≫ stackInSetsULift.map g.left :=
  StackOver.Groupoids.Hom.isoMk
    (FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
      (CartesianBasedFunctor.toBasedIso (baseChangeQuotientIsoCartesian G φ hφ g)))

/-- The `2`-commutative square with apex `[U'/R']`, top arrow `[U'/R'] ⟶ [U/R]`,
left arrow `[U'/R'] ⟶ 𝒮_{X'}`, and bottom arrow `𝒮_{X'} ⟶ 𝒮_X`. -/
def baseChangeQuotientCone {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    PseudoPullbackCone (toSpaceHom (overX G φ hφ)) (stackInSetsULift.map g.left) where
  pt := fppfQuotientStack (transportedBaseChange G φ hφ g)
  fst := baseChangeQuotientMap G φ hφ g
  snd := baseChangeToSpaceHom G φ hφ g
  iso := baseChangeQuotientIso G φ hφ g

/-- The apex of `baseChangeQuotientCone` is `[U'/R']`. -/
theorem baseChangeQuotientCone_pt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientCone G φ hφ g).pt =
      fppfQuotientStack (transportedBaseChange G φ hφ g) := sorry

/-- The first projection of `baseChangeQuotientCone` is `[U'/R'] ⟶ [U/R]`. -/
theorem baseChangeQuotientCone_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientCone G φ hφ g).fst = baseChangeQuotientMap G φ hφ g := sorry

/-- The second projection of `baseChangeQuotientCone` is `[U'/R'] ⟶ 𝒮_{X'}`. -/
theorem baseChangeQuotientCone_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientCone G φ hφ g).snd = baseChangeToSpaceHom G φ hφ g := sorry

/-- The `2`-cell of `baseChangeQuotientCone` is `baseChangeQuotientIso`. -/
theorem baseChangeQuotientCone_iso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientCone G φ hφ g).iso = baseChangeQuotientIso G φ hφ g := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
