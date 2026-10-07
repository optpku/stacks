module

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

/-- The cartesian `1`-morphism `𝒮_X ⟶ 𝒮_Y` induced by a morphism of algebraic spaces, after
aligning both stacks to the Hom-universe of `[U/R]`. -/
def stackInSetsULift.map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    stackInSetsULift X ⟶ stackInSetsULift Y :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (((stackInSetsULift.down X).comp (stackInSets.map f)).comp
          (stackInSetsULift.up Y)).toBasedFunctor)

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

/-- The cartesian source functor `𝒮_R ⟶ 𝒮_U` before lifting to stacks in groupoids. -/
def sourceMapCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSetsULift G.R.left).p (stackInSetsULift G.U.left).p :=
  ((stackInSetsULift.down G.R.left).comp (stackInSets.map G.s.left)).comp
    (stackInSetsULift.up G.U.left)

/-- The cartesian target functor `𝒮_R ⟶ 𝒮_U` before lifting to stacks in groupoids. -/
def targetMapCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSetsULift G.R.left).p (stackInSetsULift G.U.left).p :=
  ((stackInSetsULift.down G.R.left).comp (stackInSets.map G.t.left)).comp
    (stackInSetsULift.up G.U.left)

/-- The source map `s : 𝒮_R ⟶ 𝒮_U` as a morphism of stacks in groupoids. -/
def sourceMap {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    stackInSetsULift G.R.left ⟶ stackInSetsULift G.U.left :=
  stackInSetsULift.map G.s.left

/-- The target map `t : 𝒮_R ⟶ 𝒮_U` as a morphism of stacks in groupoids. -/
def targetMap {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    stackInSetsULift G.R.left ⟶ stackInSetsULift G.U.left :=
  stackInSetsULift.map G.t.left

/-- The atlas `π : 𝒮_U ⟶ [U/R]` as a morphism of stacks in groupoids, after aligning `𝒮_U`. -/
def atlasULiftHom {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    stackInSetsULift G.U.left ⟶ fppfQuotientStack G :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (fppfAtlasULift G).toBasedFunctor)

/-- `atlasULiftHom` is the morphism-universe inverse of `𝒮_U` followed by `fppfAtlas`. -/
theorem atlasULiftHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    StackOver.Groupoids.Hom.toCartesianBasedFunctor (atlasULiftHom G) =
      (stackInSetsULift.down G.U.left).comp (fppfAtlas G) := sorry

/-- The fibre morphism of `[U/_p R]` associated to the groupoid inverse of an `𝒮_R`-point. -/
def sourceTargetPreInvHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (preAtlasTarget G).toFunctor.obj x ⟶ (preAtlasSource G).toFunctor.obj x where
  base := 𝟙 ((preAtlasTarget G).toFunctor.obj x).base
  fiber := SpacePointHom.ofArrow (spacePointArrow G x ≫ G.i.left) sorry sorry

/-- The underlying arrow of `sourceTargetPreInvHom` is the groupoid inverse of the scheme-valued
`R`-point. -/
theorem sourceTargetPreInvHom_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (sourceTargetPreInvHom G x).fiber.arrow = spacePointArrow G x ≫ G.i.left := sorry

/-- The two-universe equivalence of the total category of `𝒮_U`. -/
def stackInSetsULiftEquiv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackInSets G.U.left).total ≌
      Cat.twoULift.{u + 1, u, u + 1, u + 1} (stackInSets G.U.left).total :=
  Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1} (stackInSets G.U.left).total

/-- The unlifted `𝒮_R`-point underlying a universe-aligned object. -/
def sourceTargetDown {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    (stackInSets G.R.left).total :=
  (stackInSetsULift.down G.R.left).toFunctor.obj x

/-- The unlifted source image of a universe-aligned `𝒮_R`-point. -/
def sourceTargetDownSource {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    (stackInSets G.U.left).total :=
  (stackInSets.map G.s.left).toFunctor.obj (sourceTargetDown G x)

/-- The unlifted target image of a universe-aligned `𝒮_R`-point. -/
def sourceTargetDownTarget {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    (stackInSets G.U.left).total :=
  (stackInSets.map G.t.left).toFunctor.obj (sourceTargetDown G x)

/-- The component of `α : π ∘ s ⟶ π ∘ t` at a universe-aligned `𝒮_R`-point, after transporting
along the two-universe unit of `𝒮_U`. -/
def sourceTargetIsoHomApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    ((sourceMapCartesian G).comp (fppfAtlasULift G)).toFunctor.obj x ⟶
      ((targetMapCartesian G).comp (fppfAtlasULift G)).toFunctor.obj x :=
  (fppfAtlas G).toFunctor.map
      ((stackInSetsULiftEquiv G).unitIso.inv.app (sourceTargetDownSource G x)) ≫
    (fppfQuotientStackPresentation G).comparison.toFunctor.map
      (sourceTargetPreHom G (sourceTargetDown G x)) ≫
    (fppfAtlas G).toFunctor.map
      ((stackInSetsULiftEquiv G).unitIso.hom.app (sourceTargetDownTarget G x))

/-- The component of the inverse 2-cell `π ∘ t ⟶ π ∘ s` at a universe-aligned `𝒮_R`-point. -/
def sourceTargetIsoInvApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    ((targetMapCartesian G).comp (fppfAtlasULift G)).toFunctor.obj x ⟶
      ((sourceMapCartesian G).comp (fppfAtlasULift G)).toFunctor.obj x :=
  (fppfAtlas G).toFunctor.map
      ((stackInSetsULiftEquiv G).unitIso.inv.app (sourceTargetDownTarget G x)) ≫
    (fppfQuotientStackPresentation G).comparison.toFunctor.map
      (sourceTargetPreInvHom G (sourceTargetDown G x)) ≫
    (fppfAtlas G).toFunctor.map
      ((stackInSetsULiftEquiv G).unitIso.hom.app (sourceTargetDownSource G x))

/-- The cartesian `2`-isomorphism `π ∘ s ≅ π ∘ t` after aligning Hom-universes. -/
def sourceTargetIsoCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceMapCartesian G).comp (fppfAtlasULift G) ≅
      (targetMapCartesian G).comp (fppfAtlasULift G) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ sourceTargetIsoHomApp G x
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ sourceTargetIsoInvApp G x
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The invertible `2`-cell `α : π ∘ s ≅ π ∘ t` of stacks in groupoids. -/
def sourceTargetIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    sourceMap G ≫ atlasULiftHom G ≅ targetMap G ≫ atlasULiftHom G :=
  StackOver.Groupoids.Hom.isoMk
    (FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
      (CartesianBasedFunctor.toBasedIso (sourceTargetIsoCartesian G)))

/-- A component of `sourceTargetIso.hom` is the stacked image of `sourceTargetPreHom`, transported
along the two-universe unit of `𝒮_U`. -/
theorem sourceTargetIso_hom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    (CartesianBasedFunctor.toBasedNatTrans (sourceTargetIsoCartesian G).hom).toNatTrans.app x =
      sourceTargetIsoHomApp G x := sorry

/-- The `2`-commutative square with apex `𝒮_R`, legs `s` and `t`, and bottom atlas `π`. -/
def sourceTargetCone {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    PseudoPullbackCone (atlasULiftHom G) (atlasULiftHom G) where
  pt := stackInSetsULift G.R.left
  fst := sourceMap G
  snd := targetMap G
  iso := sourceTargetIso G

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

