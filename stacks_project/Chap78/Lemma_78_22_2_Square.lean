/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.AtlasSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic
public import stacks_project.Chap78.Lemma_78_20_3_Comparison
public import stacks_project.Chap78.Lemma_78_21_2_Square

/-!
# 2-cartesian square of a quotient-stack atlas

A groupoid in algebraic spaces determines cartesian functors `s, t : 𝒮_R ⟶ 𝒮_U` and
`π : 𝒮_U ⟶ [U/R]` over `(Sch/S)_fppf`, together with an invertible 2-cell
`α : π ∘ s ≅ π ∘ t`. After aligning Hom-universes, this square is a cone on the cospan
`(π, π)` whose apex is `𝒮_R`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits Opposite
open CategoryTheory.Bicategory CategoryTheory.Functor
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace


/-- The identity morphism of algebraic spaces induces the identity on the universe-aligned
`𝒮_X`. -/
theorem stackInSetsULift.map_id {S : Scheme.{u}} (X : AlgebraicSpace S) :
    stackInSetsULift.map (𝟙 X) = 𝟙 (stackInSetsULift X) := sorry

/-- Universe-aligned `𝒮`-maps preserve composition of morphisms of algebraic spaces. -/
theorem stackInSetsULift.map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    stackInSetsULift.map (f ≫ g) =
      stackInSetsULift.map f ≫ stackInSetsULift.map g := sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupoidAlgebraicSpace






/-- `atlasULiftHom` is the morphism-universe inverse of `𝒮_U` followed by `fppfAtlas`. -/
theorem atlasULiftHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    StackOver.Groupoids.Hom.toCartesianBasedFunctor (atlasULiftHom G) =
      (stackInSetsULift.down G.U.left).comp (fppfAtlas G) := sorry


/-- The underlying arrow of `sourceTargetPreInvHom` is the groupoid inverse of the scheme-valued
`R`-point. -/
theorem sourceTargetPreInvHom_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (sourceTargetPreInvHom G x).fiber.arrow = spacePointArrow G x ≫ G.i.left := sorry









/-- A component of `sourceTargetIso.hom` is the stacked image of `sourceTargetPreHom`, transported
along the two-universe unit of `𝒮_U`. -/
theorem sourceTargetIso_hom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    (CartesianBasedFunctor.toBasedNatTrans (sourceTargetIsoCartesian G).hom).toNatTrans.app x =
      sourceTargetIsoHomApp G x := sorry


/-- The apex of `sourceTargetCone G` is `𝒮_R`. -/
theorem sourceTargetCone_pt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).pt = stackInSetsULift G.R.left := sorry

/-- The first projection of `sourceTargetCone G` is `s`. -/
theorem sourceTargetCone_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).fst = sourceMap G := sorry

/-- The second projection of `sourceTargetCone G` is `t`. -/
theorem sourceTargetCone_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).snd = targetMap G := sorry

/-- The `2`-cell of `sourceTargetCone G` is `sourceTargetIso G`. -/
theorem sourceTargetCone_iso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).iso = sourceTargetIso G := sorry

/-- The based functor underlying the atlas `π`. -/
def atlasULiftBased {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackInSetsULift G.U.left).toBasedCategory ⥤ᵇ (fppfQuotientStack G).toBasedCategory :=
  StackOver.Groupoids.Hom.toBasedFunctor (atlasULiftHom G)

/-- The fibre object of `𝒮_U` over the base of `r` carried by `s(r)`. -/
def comparisonFstFiber {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : (stackInSetsULift G.R.left).total) :
    (stackInSetsULift G.U.left).p.Fiber ((stackInSetsULift G.R.left).p.obj r) :=
  Fiber.mk (congrFun (congrArg Functor.obj (sourceMapCartesian G).toBasedFunctor.w) r)

/-- The fibre object of `𝒮_U` over the base of `r` carried by `t(r)`. -/
def comparisonSndFiber {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : (stackInSetsULift G.R.left).total) :
    (stackInSetsULift G.U.left).p.Fiber ((stackInSetsULift G.R.left).p.obj r) :=
  Fiber.mk (congrFun (congrArg Functor.obj (targetMapCartesian G).toBasedFunctor.w) r)

/-- The fibrewise comparison isomorphism `π(s(r)) ≅ π(t(r))` in the fibre of `[U/R]`. -/
def comparisonFiberIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : (stackInSetsULift G.R.left).total) :
    ((atlasULiftBased G).fiberFunctor ((stackInSetsULift G.R.left).p.obj r)).obj
        (comparisonFstFiber G r) ≅
      ((atlasULiftBased G).fiberFunctor ((stackInSetsULift G.R.left).p.obj r)).obj
        (comparisonSndFiber G r) where
  hom := ⟨sourceTargetIsoHomApp G r, sorry⟩
  inv := ⟨sourceTargetIsoInvApp G r, sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The chosen two-fibre product `𝒮_U ×_{[U/R]} 𝒮_U` of the universe-aligned atlas. -/
def sourceTargetApex {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    StackOver.Groupoids.{u + 1, u, u + 1, u + 1} (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1}
    (atlasULiftHom G) (atlasULiftHom G)

/-- The explicit `4.32.3` object `(T, s(r), t(r), α(r))` of `𝒮_U ×_{[U/R]} 𝒮_U`. -/
def comparisonObj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : (stackInSetsULift G.R.left).total) :
    (sourceTargetApex G).total :=
  BasedCategory.PseudoPullback.mk (atlasULiftBased G) (atlasULiftBased G)
    ((stackInSetsULift G.R.left).p.obj r)
    { fst := comparisonFstFiber G r
      snd := comparisonSndFiber G r
      iso := comparisonFiberIso G r }

/-- The morphism of `𝒮_U ×_{[U/R]} 𝒮_U` induced by a morphism of `𝒮_R`. -/
def comparisonMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {r r' : (stackInSetsULift G.R.left).total} (φ : r ⟶ r') :
    comparisonObj G r ⟶ comparisonObj G r' :=
  BasedCategory.PseudoPullback.Hom.mk
    ((stackInSetsULift G.R.left).p.map φ)
    ((sourceMapCartesian G).toFunctor.map φ) sorry
    ((targetMapCartesian G).toFunctor.map φ) sorry sorry

/-- The total functor `𝒮_R ⟶ 𝒮_U ×_{[U/R]} 𝒮_U` sending `r` to `(T, s(r), t(r), α(r))`. -/
def comparisonTotalFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackInSetsULift G.R.left).total ⥤ (sourceTargetApex G).total where
  obj r := comparisonObj G r
  map φ := comparisonMap G φ
  map_id := sorry
  map_comp := sorry

/-- The based functor underlying `comparison`. -/
def comparisonBased {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackInSetsULift G.R.left).toBasedCategory ⥤ᵇ
      (sourceTargetApex G).toBasedCategory where
  toFunctor := comparisonTotalFunctor G
  w := sorry

/-- The source-specified functor `𝒮_R ⟶ 𝒮_U ×_{[U/R]} 𝒮_U`. -/
def comparison {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).pt ⟶ sourceTargetApex G :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (comparisonBased G))

/-- On objects, `comparison` sends `r` to the `4.32.3` object `(T, s(r), t(r), α(r))`. -/
theorem comparison_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : (stackInSetsULift G.R.left).total) :
    (StackOver.Groupoids.Hom.toFunctor (comparison G)).obj r = comparisonObj G r := sorry

/-- The first component of `comparisonObj G r` is `s(r)`. -/
theorem comparison_obj_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : (stackInSetsULift G.R.left).total) :
    BasedCategory.PseudoPullback.fstObj (comparisonObj G r) =
      (sourceMapCartesian G).toFunctor.obj r := sorry

/-- The second component of `comparisonObj G r` is `t(r)`. -/
theorem comparison_obj_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : (stackInSetsULift G.R.left).total) :
    BasedCategory.PseudoPullback.sndObj (comparisonObj G r) =
      (targetMapCartesian G).toFunctor.obj r := sorry

/-- The comparison morphism of `comparisonObj G r` is the component `α(r)`. -/
theorem comparison_obj_iso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : (stackInSetsULift G.R.left).total) :
    BasedCategory.PseudoPullback.comparison (comparisonObj G r) =
      sourceTargetIsoHomApp G r := sorry

/-- The functor `𝒮_R ⟶ 𝒮_U ×_{[U/R]} 𝒮_U` is an equivalence of stacks in groupoids. -/
theorem comparison_isEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    StackOver.Groupoids.Hom.IsEquivalence (comparison G) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
