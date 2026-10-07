module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import stacks_project.Chap94.Lemma_94_16_1_QuotientMap
public import stacks_project.Chap100.Lemma_100_9_7_Subspace
public import stacks_project.Chap100.Lemma_100_9_8_QuotientMap

/-!
# Presentation of an immersion into a quotient stack

The recovered subspace `Z ⊂ U` of an immersion `i : Z ⟶ [U / R]` has restriction `R_Z`.
The atlas `U' ⟶ Z` of the 2-fibre product descends along stackification of `[Z /ₚ R_Z]`
to a presentation `[Z / R_Z] ⟶ Z`, and the resulting triangle with `restrictQuotientHom`
is 2-commutative.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open Functor Opposite Bicategory BasedNatIso
open scoped Bicategory CategoricalPullback CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The pulled-back atlas `U' ⟶ Z`, as the second projection of the 2-fibre product after
presenting `objectApex`. -/
def restrictedAtlas {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ G.quotientStack)
    [Immersion i] : (objectSpace G i).toGroupoids ⟶ Z :=
  (AlgebraicStack.representingEquiv (objectApex_isRepresentable G i)).inv ≫
    TwoFibreProduct.snd.{u + 1, u, u + 1, u} G.atlas i

/-- `restrictedAtlas` is `representingEquiv.inv` followed by the second projection. -/
theorem restrictedAtlas_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    restrictedAtlas G i =
      (AlgebraicStack.representingEquiv (objectApex_isRepresentable G i)).inv ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} G.atlas i :=
  sorry

/-- The 1-morphism of presented groupoid fibrations associated to the recovered inclusion. -/
def objectInclusionToGroupoids {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (objectSpace G i).toGroupoids ⟶ G.U.left.toGroupoids :=
  toGroupoids.map (objectInclusion G i)

/-- Transporting the recovered inclusion through `toGroupoids` recovers the first projection of
the 2-fibre product, up to the representing equivalence of `objectApex`. -/
def objectInclusionToGroupoids_iso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    objectInclusionToGroupoids G i ≅
      (AlgebraicStack.representingEquiv (objectApex_isRepresentable G i)).inv ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} G.atlas i :=
  (AlgebraicStack.evalMapIso
      ((AlgebraicStack.representingEquiv (objectApex_isRepresentable G i)).inv ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} G.atlas i)).symm

/-- Atlas comparison `objectInclusion ≫ G.atlas ≅ restrictedAtlas ≫ i`, as
`TwoFibreProduct.comparisonIso G.atlas i` transported along `representingEquiv`. -/
def objectInclusion_comp_atlas {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    objectInclusionToGroupoids G i ≫ G.atlas ≅ restrictedAtlas G i ≫ i :=
  whiskerRightIso (objectInclusionToGroupoids_iso G i) G.atlas ≪≫
    (α_ (AlgebraicStack.representingEquiv (objectApex_isRepresentable G i)).inv
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} G.atlas i) G.atlas).symm ≪≫
    whiskerLeftIso (AlgebraicStack.representingEquiv (objectApex_isRepresentable G i)).inv
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} G.atlas i) ≪≫
    α_ (AlgebraicStack.representingEquiv (objectApex_isRepresentable G i)).inv
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} G.atlas i) i

/-- The image of a co-Grothendieck object of `[Z /ₚ R_Z]` in the fibre of `Z`. -/
def presentationHomPreFiber {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    (a : (restrict G (subspace G i)).preQuotient.total) : Z.p.Fiber a.base :=
  (fiberFunctor (restrictedAtlas G i) a.base).obj (pointAsPresentedFiber a.fiber)

/-- `presentationHomPreFiber` applies `restrictedAtlas` to the underlying `U'`-point. -/
theorem presentationHomPreFiber_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    (a : (restrict G (subspace G i)).preQuotient.total) :
    presentationHomPreFiber G i a =
      (fiberFunctor (restrictedAtlas G i) a.base).obj (pointAsPresentedFiber a.fiber) :=
  sorry

/-- The source `U'`-point of a co-Grothendieck arrow, as the source of `φ.fiber`. -/
def presentationHomPreSourceU {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (objectSpace G i).toGroupoids.p.Fiber a.base :=
  pointAsPresentedFiber ((restrict G (subspace G i)).s.left.app (op a.base) φ.fiber.arrow)

/-- The target `U'`-point of a co-Grothendieck arrow over `a.base`, as the target of `φ.fiber`. -/
def presentationHomPreTargetU {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (objectSpace G i).toGroupoids.p.Fiber a.base :=
  pointAsPresentedFiber ((restrict G (subspace G i)).t.left.app (op a.base) φ.fiber.arrow)

/-- The source of `φ.fiber` is the presented `U'`-point of the co-Grothendieck source. -/
def presentationHomPreSourceUIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    presentationHomPreSourceU G i φ ≅ pointAsPresentedFiber a.fiber :=
  eqToIso (congrArg pointAsPresentedFiber φ.fiber.source)

/-- The target of `φ.fiber` is the restriction of the presented target `U'`-point. -/
def presentationHomPreTargetRestrictIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    presentationHomPreTargetU G i φ ≅
      pointAsPresentedFiber
        ((restrict G (subspace G i)).U.left.functorOfPoints.map φ.base.op b.fiber) :=
  eqToIso (congrArg pointAsPresentedFiber φ.fiber.target)

/-- Restriction of a presented `U'`-point along `φ.base` is selected reindexing in `U'`. -/
theorem presentationHomPreTarget_eq_reindex {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    pointAsPresentedFiber
        ((restrict G (subspace G i)).U.left.functorOfPoints.map φ.base.op b.fiber) =
      Chosen.reindexObj (objectSpace G i).toGroupoids.p φ.base
        (pointAsPresentedFiber b.fiber) :=
  sorry

/-- Selected-cleavage comparison identifying restriction of a presented `U'`-point with
reindexing in `U'`. -/
def presentationHomPreTargetReindexIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    pointAsPresentedFiber
        ((restrict G (subspace G i)).U.left.functorOfPoints.map φ.base.op b.fiber) ≅
      Chosen.reindexObj (objectSpace G i).toGroupoids.p φ.base
        (pointAsPresentedFiber b.fiber) :=
  eqToIso (presentationHomPreTarget_eq_reindex G i φ)

/-- Composite identification of the target of `φ.fiber` with the selected reindexing of the
presented target. -/
def presentationHomPreTargetUIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    presentationHomPreTargetU G i φ ≅
      Chosen.reindexObj (objectSpace G i).toGroupoids.p φ.base
        (pointAsPresentedFiber b.fiber) :=
  presentationHomPreTargetRestrictIso G i φ ≪≫ presentationHomPreTargetReindexIso G i φ

/-- Selected-cleavage comparison `φ.base⁎ (restrictedAtlas(b)) ≅ restrictedAtlas(φ.base⁎ b)`. -/
def presentationHomPreReindexIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    Chosen.reindexObj Z.p φ.base (presentationHomPreFiber G i b) ≅
      (fiberFunctor (restrictedAtlas G i) a.base).obj
        (Chosen.reindexObj (objectSpace G i).toGroupoids.p φ.base
          (pointAsPresentedFiber b.fiber)) :=
  CartesianBasedFunctor.Reindex.mapIso
    (toCartesianBasedFunctor (restrictedAtlas G i))
    (Cleavage.ofIsFibered (objectSpace G i).toGroupoids.p)
    (Cleavage.ofIsFibered Z.p) φ.base (pointAsPresentedFiber b.fiber)

/-- `presentationHomPreReindexIso` is the selected-cleavage reindexing comparison of
`restrictedAtlas`. -/
theorem presentationHomPreReindexIso_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    presentationHomPreReindexIso G i φ =
      CartesianBasedFunctor.Reindex.mapIso
        (toCartesianBasedFunctor (restrictedAtlas G i))
        (Cleavage.ofIsFibered (objectSpace G i).toGroupoids.p)
        (Cleavage.ofIsFibered Z.p) φ.base (pointAsPresentedFiber b.fiber) :=
  sorry

/-- The `G.R`-point associated to the fibre of `φ` by the restriction morphism of
groupoids. -/
def presentationHomPreArrowG {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    G.R.left.functorOfPoints.obj (op a.base) :=
  (restrictHom G (subspace G i)).arrow.left.app (op a.base) φ.fiber.arrow

/-- The `G.R`-point of `φ.fiber` as a total object of the presented arrow space. -/
def presentationHomPreArrowGTotal {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    G.R.left.toGroupoids.total :=
  (pointAsPresentedFiber (presentationHomPreArrowG G i φ)).1

/-- The fibre morphism of `[U /ₚ R]` associated to an `R`-point, with underlying arrow that
point itself. -/
def presentationSourceTargetPreHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : G.R.left.toGroupoids.total) :
    (toFunctor (toGroupoids.map G.s.left ≫ G.atlasToPreQuotient)).obj x ⟶
      (toFunctor (toGroupoids.map G.t.left ≫ G.atlasToPreQuotient)).obj x where
  base := 𝟙 _
  fiber := FunctorPointHom.ofArrow x.unop.snd sorry sorry

/-- The inverse fibre morphism of `[U /ₚ R]` associated to an `R`-point, with underlying arrow
the groupoid inverse of that point. -/
def presentationSourceTargetPreInvHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : G.R.left.toGroupoids.total) :
    (toFunctor (toGroupoids.map G.t.left ≫ G.atlasToPreQuotient)).obj x ⟶
      (toFunctor (toGroupoids.map G.s.left ≫ G.atlasToPreQuotient)).obj x where
  base := 𝟙 _
  fiber :=
    FunctorPointHom.ofArrow (G.i.left.app (op x.unop.fst.unop) x.unop.snd) sorry sorry

/-- Componentwise `2`-isomorphism `πₚ ∘ s ≅ πₚ ∘ t` on `[U /ₚ R]`. -/
def presentationSourceTargetPreApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : G.R.left.toGroupoids.total) :
    (toFunctor (toGroupoids.map G.s.left ≫ G.atlasToPreQuotient)).obj x ≅
      (toFunctor (toGroupoids.map G.t.left ≫ G.atlasToPreQuotient)).obj x where
  hom := presentationSourceTargetPreHom G x
  inv := presentationSourceTargetPreInvHom G x
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical `2`-isomorphism `s ≫ atlasToPreQuotient ≅ t ≫ atlasToPreQuotient`. -/
def presentationSourceTargetPreIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    toGroupoids.map G.s.left ≫ G.atlasToPreQuotient ≅
      toGroupoids.map G.t.left ≫ G.atlasToPreQuotient :=
  BasedFunctorIso.lift
    (ofComponents (presentationSourceTargetPreApp G) (fun {_ _} _ ↦ sorry)
      (fun _ ↦ sorry))

/-- The canonical `2`-isomorphism `s ≫ atlas ≅ t ≫ atlas` on the quotient stack. -/
def presentationAtlasSourceTargetIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    toGroupoids.map G.s.left ≫ G.atlas ≅ toGroupoids.map G.t.left ≫ G.atlas :=
  (α_ (toGroupoids.map G.s.left) G.atlasToPreQuotient G.stackificationHom).symm ≪≫
    whiskerRightIso (presentationSourceTargetPreIso G) G.stackificationHom ≪≫
    α_ (toGroupoids.map G.t.left) G.atlasToPreQuotient G.stackificationHom

/-- Atlas comparison `s ≫ atlas ≅ t ≫ atlas` at the `G.R`-point of `φ.fiber`. -/
def presentationHomPreAtlasSourceTargetApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor (toGroupoids.map G.s.left ≫ G.atlas)).obj
        (presentationHomPreArrowGTotal G i φ) ≅
      (toFunctor (toGroupoids.map G.t.left ≫ G.atlas)).obj
        (presentationHomPreArrowGTotal G i φ) :=
  (BasedNatIso.toNatIso
      (toBasedFunctorIso (presentationAtlasSourceTargetIso G))).app
    (presentationHomPreArrowGTotal G i φ)

/-- Objectwise atlas comparison `objectInclusion ≫ atlas ≅ restrictedAtlas ≫ i` at the source
of `φ.fiber`. -/
def presentationHomPreSourceComparisonApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor (objectInclusionToGroupoids G i ≫ G.atlas)).obj
        (presentationHomPreSourceU G i φ).1 ≅
      (toFunctor (restrictedAtlas G i ≫ i)).obj (presentationHomPreSourceU G i φ).1 :=
  (BasedNatIso.toNatIso (toBasedFunctorIso (objectInclusion_comp_atlas G i))).app
    (presentationHomPreSourceU G i φ).1

/-- Objectwise atlas comparison `objectInclusion ≫ atlas ≅ restrictedAtlas ≫ i` at the target
of `φ.fiber`. -/
def presentationHomPreTargetComparisonApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor (objectInclusionToGroupoids G i ≫ G.atlas)).obj
        (presentationHomPreTargetU G i φ).1 ≅
      (toFunctor (restrictedAtlas G i ≫ i)).obj (presentationHomPreTargetU G i φ).1 :=
  (BasedNatIso.toNatIso (toBasedFunctorIso (objectInclusion_comp_atlas G i))).app
    (presentationHomPreTargetU G i φ).1

/-- On objects, the source of the `G.R`-point of `φ.fiber` recovers `objectInclusion` of the
source of `φ.fiber`. -/
theorem presentationHomPre_source_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor (toGroupoids.map G.s.left ≫ G.atlas)).obj
        (presentationHomPreArrowGTotal G i φ) =
      (toFunctor (objectInclusionToGroupoids G i ≫ G.atlas)).obj
        (presentationHomPreSourceU G i φ).1 :=
  sorry

/-- On objects, the target of the `G.R`-point of `φ.fiber` recovers `objectInclusion` of the
target of `φ.fiber`. -/
theorem presentationHomPre_target_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor (toGroupoids.map G.t.left ≫ G.atlas)).obj
        (presentationHomPreArrowGTotal G i φ) =
      (toFunctor (objectInclusionToGroupoids G i ≫ G.atlas)).obj
        (presentationHomPreTargetU G i φ).1 :=
  sorry

/-- Applying `i` to `restrictedAtlas` of the source of `φ.fiber` recovers the composite
`restrictedAtlas ≫ i`. -/
theorem presentationHomPre_i_source_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor i).obj
        ((fiberFunctor (restrictedAtlas G i) a.base).obj
          (presentationHomPreSourceU G i φ)).1 =
      (toFunctor (restrictedAtlas G i ≫ i)).obj (presentationHomPreSourceU G i φ).1 :=
  sorry

/-- Applying `i` to `restrictedAtlas` of the target of `φ.fiber` recovers the composite
`restrictedAtlas ≫ i`. -/
theorem presentationHomPre_i_target_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor i).obj
        ((fiberFunctor (restrictedAtlas G i) a.base).obj
          (presentationHomPreTargetU G i φ)).1 =
      (toFunctor (restrictedAtlas G i ≫ i)).obj (presentationHomPreTargetU G i φ).1 :=
  sorry

/-- An immersion is bijective on morphisms of total categories. -/
theorem presentationHomPre_i_map_bijective {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] (x y : Z.total) :
    Function.Bijective
      ((toFunctor i).map : (x ⟶ y) → ((toFunctor i).obj x ⟶ (toFunctor i).obj y)) :=
  sorry

/-- The Hom-equivalence of an immersion on total-category morphisms. -/
def presentationHomPre_i_homEquiv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] (x y : Z.total) :
    (x ⟶ y) ≃ ((toFunctor i).obj x ⟶ (toFunctor i).obj y) :=
  Equiv.ofBijective _ (presentationHomPre_i_map_bijective G i x y)

/-- The image in `[U / R]` of the vertical comparison of `φ.fiber`, as
`TwoFibreProduct.comparisonIso G.atlas i` conjugated with the source-target cell of `G`. -/
def presentationHomPreImageIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor i).obj
        ((fiberFunctor (restrictedAtlas G i) a.base).obj
          (presentationHomPreTargetU G i φ)).1 ≅
      (toFunctor i).obj
        ((fiberFunctor (restrictedAtlas G i) a.base).obj
          (presentationHomPreSourceU G i φ)).1 :=
  eqToIso (presentationHomPre_i_target_obj G i φ) ≪≫
    (presentationHomPreTargetComparisonApp G i φ).symm ≪≫
    (eqToIso (presentationHomPre_target_obj G i φ)).symm ≪≫
    (presentationHomPreAtlasSourceTargetApp G i φ).symm ≪≫
    eqToIso (presentationHomPre_source_obj G i φ) ≪≫
    presentationHomPreSourceComparisonApp G i φ ≪≫
    (eqToIso (presentationHomPre_i_source_obj G i φ)).symm

/-- The vertical comparison of `φ.fiber` in `Z`, obtained by lifting
`presentationHomPreImageIso` along the immersion `i`. -/
def presentationHomPreAmbientIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    ((fiberFunctor (restrictedAtlas G i) a.base).obj
        (presentationHomPreTargetU G i φ)).1 ≅
      ((fiberFunctor (restrictedAtlas G i) a.base).obj
        (presentationHomPreSourceU G i φ)).1 where
  hom :=
    (presentationHomPre_i_homEquiv G i
        ((fiberFunctor (restrictedAtlas G i) a.base).obj
          (presentationHomPreTargetU G i φ)).1
        ((fiberFunctor (restrictedAtlas G i) a.base).obj
          (presentationHomPreSourceU G i φ)).1).symm
      (presentationHomPreImageIso G i φ).hom
  inv :=
    (presentationHomPre_i_homEquiv G i
        ((fiberFunctor (restrictedAtlas G i) a.base).obj
          (presentationHomPreSourceU G i φ)).1
        ((fiberFunctor (restrictedAtlas G i) a.base).obj
          (presentationHomPreTargetU G i φ)).1).symm
      (presentationHomPreImageIso G i φ).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Fibrewise comparison `restrictedAtlas(t(r)) ≅ restrictedAtlas(s(r))` of the fibre of
`φ`. -/
def presentationHomPreKernelComparison {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (fiberFunctor (restrictedAtlas G i) a.base).obj (presentationHomPreTargetU G i φ) ≅
      (fiberFunctor (restrictedAtlas G i) a.base).obj (presentationHomPreSourceU G i φ) :=
  Functor.Fiber.isoMk (presentationHomPreAmbientIso G i φ) sorry

/-- The switched comparison isomorphism `α : restrictedAtlas(φ.base⁎ b) ≅ restrictedAtlas(a)`
obtained by transporting the source-target comparison of `φ.fiber` to the presented objects of
`U'`. -/
def presentationHomPreAlpha {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (fiberFunctor (restrictedAtlas G i) a.base).obj
        (Chosen.reindexObj (objectSpace G i).toGroupoids.p φ.base
          (pointAsPresentedFiber b.fiber)) ≅
      (fiberFunctor (restrictedAtlas G i) a.base).obj (pointAsPresentedFiber a.fiber) :=
  ((fiberFunctor (restrictedAtlas G i) a.base).mapIso
      (presentationHomPreTargetUIso G i φ)).symm ≪≫
    presentationHomPreKernelComparison G i φ ≪≫
    (fiberFunctor (restrictedAtlas G i) a.base).mapIso (presentationHomPreSourceUIso G i φ)

/-- The switched comparison triple `(b, a, α)` on presented objects of `U'`. -/
def presentationHomPreSwitched {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (fiberFunctor (restrictedAtlas G i) a.base) ⊡
      (fiberFunctor (restrictedAtlas G i) a.base) :=
  ofSwitchedComparison (restrictedAtlas G i) (pointAsPresentedFiber a.fiber)
    (Chosen.reindexObj (objectSpace G i).toGroupoids.p φ.base
      (pointAsPresentedFiber b.fiber))
    (presentationHomPreAlpha G i φ)

/-- The vertical image of a co-Grothendieck fibre: `canonicalHom` of the switched comparison
of `φ.fiber`, composed with the reindexing comparison of `restrictedAtlas`. -/
def presentationHomPreVertical {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (presentationHomPreFiber G i a).1 ⟶
      (Chosen.reindexObj Z.p φ.base (presentationHomPreFiber G i b)).1 :=
  (canonicalHom (restrictedAtlas G i) (presentationHomPreSwitched G i φ)).1 ≫
    (presentationHomPreReindexIso G i φ).inv.1

/-- The total-category functor of the prestack map `[Z /ₚ R_Z] ⟶ Z` induced by
`restrictedAtlas`. On objects it sends a `T`-point of `U'` to `restrictedAtlas` of the
corresponding object. On a co-Grothendieck arrow `φ` it sends the fibre component to
`canonicalHom` of the switched comparison of `φ.fiber` and then composes with the selected
cartesian lift of `φ.base`. -/
def presentationHomPreTotal {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (restrict G (subspace G i)).preQuotient.total ⥤ Z.total where
  obj a := (presentationHomPreFiber G i a).1
  map {a b} φ :=
    presentationHomPreVertical G i φ ≫
      Chosen.cartesianHom Z.p φ.base (presentationHomPreFiber G i b)
  map_id := sorry
  map_comp := sorry

/-- On morphisms, `presentationHomPreTotal` composes the vertical `canonicalHom` image of
`φ.fiber` with the selected cartesian lift of `φ.base`. -/
theorem presentationHomPreTotal_map_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (presentationHomPreTotal G i).map φ =
      (canonicalHom (restrictedAtlas G i) (presentationHomPreSwitched G i φ)).1 ≫
        (presentationHomPreReindexIso G i φ).inv.1 ≫
        Chosen.cartesianHom Z.p φ.base (presentationHomPreFiber G i b) :=
  sorry

/-- The prestack map `[Z /ₚ R_Z] ⟶ Z` commutes strictly with the projections to `Over S`. -/
theorem presentationHomPreTotal_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    presentationHomPreTotal G i ⋙ Z.p = (restrict G (subspace G i)).preQuotient.p :=
  sorry

/-- The 1-morphism `[Z /ₚ R_Z] ⟶ Z` induced by `restrictedAtlas`. -/
def presentationHomPre {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (restrict G (subspace G i)).preQuotient ⟶ Z :=
  ofBasedFunctor
    (BasedFunctor.ofFunctor (presentationHomPreTotal G i) (presentationHomPreTotal_w G i))

/-- The cartesian based functor underlying `presentationHomPre`. -/
def presentationHomPreCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    CartesianBasedFunctor (restrict G (subspace G i)).preQuotient.p Z.p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (presentationHomPreTotal G i) (presentationHomPreTotal_w G i))

/-- The selected stackification lift of `presentationHomPre` through `[Z /ₚ R_Z] ⟶ [Z / R_Z]`. -/
def presentationHomLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (restrict G (subspace G i)).stackificationPresentation.comparison)
      (presentationHomPreCartesian G i) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (restrict G (subspace G i)).stackificationPresentation.isStackification
    (presentationHomPreCartesian G i)

/-- The presentation 1-morphism `[Z / R_Z] ⟶ Z` obtained by stackifying `restrictedAtlas`. -/
def presentationHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (restrict G (subspace G i)).quotientStack ⟶ Z :=
  ofBasedFunctor (CartesianBasedFunctor.toBasedFunctor (presentationHomLift G i).lift)

/-- `presentationHom` is the groupoid-fibred morphism associated to the selected stackification
lift of `presentationHomPreCartesian`. -/
theorem presentationHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    toBasedFunctor (presentationHom G i) =
      CartesianBasedFunctor.toBasedFunctor (presentationHomLift G i).lift :=
  sorry

/-- Precomposing `presentationHom` with stackification of `[Z /ₚ R_Z]` recovers
`presentationHomPre`. -/
def presentationHom_isLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (restrict G (subspace G i)).stackificationHom ≫ presentationHom G i ≅
      presentationHomPre G i :=
  BasedFunctorIso.lift (CartesianBasedFunctor.toBasedIso (presentationHomLift G i).comparison)

/-- On objects, precomposition of `presentationHomPre` with `atlasToPreQuotient` recovers
`restrictedAtlas`. -/
theorem atlasToPreQuotient_comp_presentationHomPre_obj {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) [Smooth G]
    {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ G.quotientStack) [Immersion i]
    (x : (objectSpace G i).toGroupoids.total) :
    (toFunctor
        ((restrict G (subspace G i)).atlasToPreQuotient ≫ presentationHomPre G i)).obj x =
      (toFunctor (restrictedAtlas G i)).obj x :=
  sorry

/-- After presenting `U'`, the prestack map induced by `restrictedAtlas` recovers
`restrictedAtlas` on the object space. -/
def atlasToPreQuotient_comp_presentationHomPre {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (restrict G (subspace G i)).atlasToPreQuotient ≫ presentationHomPre G i ≅
      restrictedAtlas G i :=
  BasedFunctorIso.lift
    (ofComponents (fun x ↦ eqToIso (atlasToPreQuotient_comp_presentationHomPre_obj G i x))
      (fun {_ _} _ ↦ sorry) (fun _ ↦ sorry))

/-- The restricted atlas identifies with the composite of the restriction atlas and
`presentationHom`. -/
def restrictedAtlas_comp_iso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (restrict G (subspace G i)).atlas ≫ presentationHom G i ≅ restrictedAtlas G i :=
  (α_ (restrict G (subspace G i)).atlasToPreQuotient
      (restrict G (subspace G i)).stackificationHom (presentationHom G i)).symm ≪≫
    whiskerLeftIso (restrict G (subspace G i)).atlasToPreQuotient
      (presentationHom_isLift G i) ≪≫
    atlasToPreQuotient_comp_presentationHomPre G i

/-- Restriction of a smooth groupoid to the invariant subspace cut out by `i` remains smooth. -/
instance instSmooth_restrict_subspace {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    Smooth (restrict G (subspace G i)) :=
  sorry

/-- The quotient stack of the restriction to the invariant subspace cut out by `i` is an
algebraic stack. -/
instance instAlgebraicStack_restrictQuotient_subspace {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    AlgebraicStack (restrict G (subspace G i)).quotientStack :=
  sorry

/-- The presentation `[Z / R_Z] ⟶ Z` is an equivalence of groupoid fibrations. -/
instance instIsEquivalence_presentationHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (toBasedFunctor (presentationHom G i)).IsEquivalence :=
  sorry

/-- Precomposition with stackification of `[Z /ₚ R_Z]` is an equivalence on morphisms into
`[U / R]`. -/
instance instIsEquivalence_stackification_precomp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (Bicategory.precomp G.quotientStack
        (restrict G (subspace G i)).stackificationHom).IsEquivalence :=
  sorry

/-- The Hom-equivalence on morphisms into `[U / R]` induced by stackification of
`[Z /ₚ R_Z]`. -/
def stackification_homEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    ((restrict G (subspace G i)).quotientStack ⟶ G.quotientStack) ≌
      ((restrict G (subspace G i)).preQuotient ⟶ G.quotientStack) :=
  Functor.asEquivalence
    (Bicategory.precomp G.quotientStack (restrict G (subspace G i)).stackificationHom)

/-- Precomposing `restrictQuotientHom` with stackification of `[Z /ₚ R_Z]` recovers the
prestack map induced by `restrictHom`. -/
def restrictQuotientHom_isLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (restrict G (subspace G i)).stackificationHom ≫ restrictQuotientHom G (subspace G i) ≅
      Hom.preQuotientMap (restrictHom G (subspace G i)) ≫ G.stackificationHom :=
  BasedFunctorIso.lift
    (CartesianBasedFunctor.toBasedIso (Hom.quotientStackHom_comp (restrictHom G (subspace G i))))

/-- Objectwise atlas comparison `objectInclusion ≫ atlas ≅ restrictedAtlas ≫ i` at a point of
`U'`. -/
def presentationHomPreAtlasComparison_app {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    (u' : (objectSpace G i).toGroupoids.total) :
    (toFunctor (objectInclusionToGroupoids G i ≫ G.atlas)).obj u' ≅
      (toFunctor (restrictedAtlas G i ≫ i)).obj u' :=
  (BasedNatIso.toNatIso (toBasedFunctorIso (objectInclusion_comp_atlas G i))).app u'

/-- The `U'`-point associated to a co-Grothendieck object of `[Z /ₚ R_Z]`. -/
def presentationHomPre_apexPoint {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    (x : (restrict G (subspace G i)).preQuotient.total) :
    (objectSpace G i).toGroupoids.total :=
  (pointAsPresentedFiber x.fiber).1

/-- On objects, `pr_pre ≫ stackification` recovers `objectInclusion ≫ atlas` at the associated
apex point. -/
theorem presentationHomPre_comp_obj_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    (x : (restrict G (subspace G i)).preQuotient.total) :
    (toFunctor
        (Hom.preQuotientMap (restrictHom G (subspace G i)) ≫ G.stackificationHom)).obj x =
      (toFunctor (objectInclusionToGroupoids G i ≫ G.atlas)).obj
        (presentationHomPre_apexPoint G i x) :=
  sorry

/-- On objects, `presentationHomPre ≫ i` recovers `restrictedAtlas ≫ i` at the associated apex
point. -/
theorem presentationHomPre_comp_obj_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    (x : (restrict G (subspace G i)).preQuotient.total) :
    (toFunctor (presentationHomPre G i ≫ i)).obj x =
      (toFunctor (restrictedAtlas G i ≫ i)).obj (presentationHomPre_apexPoint G i x) :=
  sorry

/-- Component of the prestack functoriality cell at a co-Grothendieck point: the atlas
`comparisonIso` at the associated point of `U'`, conjugated by the object identifications of
`pr_pre ≫ stackification` and `presentationHomPre ≫ i`. -/
def presentationHomPre_comp_app {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    (x : (restrict G (subspace G i)).preQuotient.total) :
    (toFunctor
        (Hom.preQuotientMap (restrictHom G (subspace G i)) ≫ G.stackificationHom)).obj x ≅
      (toFunctor (presentationHomPre G i ≫ i)).obj x :=
  eqToIso (presentationHomPre_comp_obj_fst G i x) ≪≫
    presentationHomPreAtlasComparison_app G i (presentationHomPre_apexPoint G i x) ≪≫
    (eqToIso (presentationHomPre_comp_obj_snd G i x)).symm

/-- Naturality of the prestack components. The fibre-arrow case uses the canonical-arrow
formula of `presentationHomPreTotal` and the atlas comparison
`TwoFibreProduct.comparisonIso G.atlas i`. -/
theorem presentationHomPre_comp_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i]
    {a b : (restrict G (subspace G i)).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor
          (Hom.preQuotientMap (restrictHom G (subspace G i)) ≫ G.stackificationHom)).map φ ≫
        (presentationHomPre_comp_app G i b).hom =
      (presentationHomPre_comp_app G i a).hom ≫
        (toFunctor (presentationHomPre G i ≫ i)).map φ :=
  sorry

/-- The prestack map induced by `restrictHom`, after stackifying the target, is 2-isomorphic to
`presentationHomPre` postcomposed with `i`. The atlas-level cell is
`TwoFibreProduct.comparisonIso G.atlas i`. -/
def presentationHomPre_comp_iso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    Hom.preQuotientMap (restrictHom G (subspace G i)) ≫ G.stackificationHom ≅
      presentationHomPre G i ≫ i :=
  BasedFunctorIso.lift
    (ofComponents (presentationHomPre_comp_app G i)
      (presentationHomPre_comp_naturality G i) (fun _ ↦ sorry))

/-- The two composites of the source triangle agree after precomposition with stackification of
`[Z /ₚ R_Z]`. -/
def triangleIso_precomp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (restrict G (subspace G i)).stackificationHom ≫ restrictQuotientHom G (subspace G i) ≅
      (restrict G (subspace G i)).stackificationHom ≫ presentationHom G i ≫ i :=
  restrictQuotientHom_isLift G i ≪≫
    presentationHomPre_comp_iso G i ≪≫
    whiskerRightIso (presentationHom_isLift G i).symm i ≪≫
    α_ (restrict G (subspace G i)).stackificationHom (presentationHom G i) i

/-- The 2-commutativity of the triangle `[Z / R_Z] ⟶ Z ⟶ [U / R]` with left-down arrow
`restrictQuotientHom`. -/
def triangleIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ G.quotientStack)
    [Immersion i] :
    restrictQuotientHom G (subspace G i) ≅ presentationHom G i ≫ i :=
  (stackification_homEquivalence G i).fullyFaithfulFunctor.preimageIso (triangleIso_precomp G i)

/-- The forward cell of `triangleIso` recovers `triangleIso_precomp` after precomposition with
stackification. -/
theorem triangleIso_hom_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    (Bicategory.precomp G.quotientStack
          (restrict G (subspace G i)).stackificationHom).map
        (triangleIso G i).hom = (triangleIso_precomp G i).hom :=
  (stackification_homEquivalence G i).fullyFaithfulFunctor.map_preimage _

end AlgebraicGeometry.GroupoidAlgebraicSpace
