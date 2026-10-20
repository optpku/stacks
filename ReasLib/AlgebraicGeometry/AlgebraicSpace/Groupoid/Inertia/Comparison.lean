/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Objects
public import ReasLib.CategoryTheory.Inertia.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Atlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Inertia.Presentation

/-!
# Comparison of inertia of a quotient stack with the inertia presentation

A pair `(x, g)` in the inertia of `[U/_p R]` over `T` is a `T`-point of the stabilizer,
and an intertwiner is a `T`-point of `R'`. This yields a cartesian functor
`I_{[U/_p R]} ⟶ [G/_p R']`. After stackification, there exists a cartesian
equivalence `I_{[U/R]} ⟶ [G/R']`.
-/

@[expose] public section

-- Local declaration justification (module visibility): exposed pullback and over-category
-- constructions reference private compatibility proof arguments. Their computational maps
-- remain explicit; this option only permits those private proof dependencies.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits
open Functor.IsFibered.InGroupoids.Stackification
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The scheme over `B` associated to the underlying object of an inertia point of
`[U/_p R]`. -/
def preInertiaBaseOver {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (ξ : RelativeInertia (preQuotient G).p) : Over B :=
  Over.mk (ξ.obj.fiber ≫ G.U.hom)

/-- The automorphism arrow of an inertia point lies over `B`. -/
private theorem preInertiaAutArrow_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (ξ : RelativeInertia (preQuotient G).p) :
    ξ.aut.hom.fiber.arrow ≫ G.R.hom = ξ.obj.fiber ≫ G.U.hom :=
  sorry

/-- The automorphism of an inertia point of `[U/_p R]`, as an arrow of `R` over `B`. -/
def preInertiaAutArrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (ξ : RelativeInertia (preQuotient G).p) : preInertiaBaseOver G ξ ⟶ G.R :=
  Over.homMk ξ.aut.hom.fiber.arrow (preInertiaAutArrow_over G ξ)

/-- The underlying object of an inertia point of `[U/_p R]`, as a point of `U` over `B`. -/
def preInertiaObjMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (ξ : RelativeInertia (preQuotient G).p) : preInertiaBaseOver G ξ ⟶ G.U :=
  Over.homMk ξ.obj.fiber rfl

/-- The automorphism of an inertia point of `[U/_p R]` is a stabilizer element. -/
private theorem preInertiaStabilizer_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (ξ : RelativeInertia (preQuotient G).p) :
    preInertiaAutArrow G ξ ≫ G.toPreRelation.hom =
      preInertiaObjMap G ξ ≫ diag G.U :=
  sorry

/-- The `T`-point of the stabilizer associated to an object of `I_{[U/_p R]}`. -/
def preInertiaStabilizer {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (ξ : RelativeInertia (preQuotient G).p) :
    preInertiaBaseOver G ξ ⟶ G.toPreRelation.stabilizer.left :=
  pullback.lift (preInertiaAutArrow G ξ) (preInertiaObjMap G ξ)
    (preInertiaStabilizer_condition G ξ)

/-- An intertwiner of inertia points lies over `B`. -/
private theorem preInertiaHomArrow_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {ξ η : RelativeInertia (preQuotient G).p} (f : ξ ⟶ η) :
    (RelativeInertia.hom f).fiber.arrow ≫ G.R.hom = ξ.obj.fiber ≫ G.U.hom :=
  sorry

/-- An intertwiner in `I_{[U/_p R]}` as an arrow of `R` over `B`. -/
def preInertiaHomArrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {ξ η : RelativeInertia (preQuotient G).p} (f : ξ ⟶ η) :
    preInertiaBaseOver G ξ ⟶ G.R :=
  Over.homMk (RelativeInertia.hom f).fiber.arrow (preInertiaHomArrow_over G f)

/-- An intertwiner and the source stabilizer element define a point of `R'`. -/
private theorem preInertiaHomLift_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {ξ η : RelativeInertia (preQuotient G).p} (f : ξ ⟶ η) :
    (preInertiaHomArrow G f ≫ G.s) =
      preInertiaStabilizer G ξ ≫ G.toPreRelation.stabilizer.hom :=
  sorry

/-- The `T`-point of `R'` associated to a morphism of `I_{[U/_p R]}`. -/
def preInertiaHomLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {ξ η : RelativeInertia (preQuotient G).p} (f : ξ ⟶ η) :
    preInertiaBaseOver G ξ ⟶ inertiaArrows G :=
  pullback.lift (preInertiaHomArrow G f) (preInertiaStabilizer G ξ)
    (preInertiaHomLift_condition G f)

/-- The object of `[G/_p R']` associated to an object of `I_{[U/_p R]}`. -/
def preInertiaComparisonObj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (ξ : RelativeInertia (preQuotient G).p) :
    (preQuotient (inertiaPresentation G)).total where
  base := ξ.obj.base
  fiber := (preInertiaStabilizer G ξ).left

/-- The morphism of `[G/_p R']` associated to a morphism of `I_{[U/_p R]}`. -/
def preInertiaComparisonMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {ξ η : RelativeInertia (preQuotient G).p} (f : ξ ⟶ η) :
    preInertiaComparisonObj G ξ ⟶ preInertiaComparisonObj G η where
  base := (RelativeInertia.hom f).base
  fiber :=
    { arrow := (preInertiaHomLift G f).left
      source := sorry
      target := sorry }

/-- The total functor `I_{[U/_p R]} ⟶ [G/_p R']` sending an automorphism of a point of
`U` to the corresponding point of the stabilizer, and an intertwiner to a point of
`R'`. -/
def preInertiaComparisonFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (FiberedCategoryOver.Groupoids.inertia (preQuotient G)).total ⥤
      (preQuotient (inertiaPresentation G)).total where
  obj := preInertiaComparisonObj G
  map := preInertiaComparisonMap G
  map_id := sorry
  map_comp := sorry

/-- `preInertiaComparisonFunctor` commutes with projection to `(Sch/S)_fppf`. -/
theorem preInertiaComparison_comm {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    preInertiaComparisonFunctor G ⋙ (preQuotient (inertiaPresentation G)).p =
      (FiberedCategoryOver.Groupoids.inertia (preQuotient G)).p :=
  sorry

/-- The cartesian `1`-morphism `I_{[U/_p R]} ⟶ [G/_p R']`. -/
def preInertiaComparison {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (FiberedCategoryOver.Groupoids.inertia (preQuotient G)).p
      (preQuotient (inertiaPresentation G)).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (preInertiaComparisonFunctor G)
      (preInertiaComparison_comm G))

/-- The total functor of `preInertiaComparison` is `preInertiaComparisonFunctor`. -/
theorem preInertiaComparison_toFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (preInertiaComparison G).toFunctor = preInertiaComparisonFunctor G :=
  sorry

/-- The cartesian functor `I_{[U/_p R]} ⟶ [G/R']` obtained by stackifying the target of
`preInertiaComparison`. -/
def preInertiaToQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (FiberedCategoryOver.Groupoids.inertia (preQuotient G)).p
      (fppfQuotientStack (inertiaPresentation G)).p :=
  (preInertiaComparison G).comp
    (fppfQuotientStackPresentation (inertiaPresentation G)).comparison

/-- Before stackification, `preInertiaComparison` is an equivalence of categories over
`(Sch/S)_fppf`. -/
theorem inertia_preQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (preInertiaComparison G).toBasedFunctor.IsEquivalence :=
  sorry

/-- There exists a cartesian equivalence from the inertia stack of a groupoid quotient
to the quotient stack of its stabilizer-conjugation groupoid over the fppf site. -/
theorem inertia_quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    ∃ F : CartesianBasedFunctor (StackOver.Groupoids.inertia (fppfQuotientStack G)).p
      (fppfQuotientStack (inertiaPresentation G)).p,
      F.toBasedFunctor.IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
