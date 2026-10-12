/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap66.Definition_66_7_2
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap76.Lemma_76_9_2_Thickening
public import stacks_project.Chap80.Lemma_80_4_6
public import stacks_project.Chap88.Definition_88_20_1_Etale
public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# Reduction of a formal algebraic space

Lemma 87.12.1 supplies a reduced algebraic space `X_red` with a representable
thickening into a formal algebraic space `X`, characterized by unique
factorization of maps from reduced algebraic spaces. This module records that
interface, constructs the induced map of reductions as that unique factor, and
identifies `X_red` with the source square `X ×_Y Y_red` by an isomorphism over
`X` when `f` is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- An algebraic space is a formal algebraic space via its functor of points. -/
instance instIsFormalAlgebraicSpace_functorOfPoints (X : AlgebraicSpace S) :
    IsFormalAlgebraicSpace X.functorOfPoints :=
  sorry

/-- The algebraic-space reduction of a formal algebraic space, in the sense of
Lemma 87.12.1: a reduced algebraic space, a representable thickening into the
formal algebraic space, and unique factorization of morphisms from reduced
algebraic spaces. -/
class Reduction (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] where
  /-- The underlying reduced algebraic space `X_red`. -/
  space : AlgebraicSpace S
  /-- The representable thickening `X_red ⟶ X`. -/
  ι : space.functorOfPoints ⟶ X
  /-- The reduction is reduced in the étale-local sense. -/
  isReduced : AlgebraicSpace.hasEtaleLocal
    (IsReduced : ObjectProperty Scheme.{u}) space
  /-- The structure morphism is representable by algebraic spaces. -/
  representable : AlgebraicSpace.representableByAlgebraicSpaces ι
  /-- Yoneda pullbacks of the structure morphism are thickenings. -/
  isThickening : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ X),
    AlgebraicSpace.IsThickening
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ)
  /-- A morphism from a reduced algebraic space into `X` factors uniquely
  through the reduction. -/
  liftUnique {U : AlgebraicSpace S}
    (hU : AlgebraicSpace.hasEtaleLocal
      (IsReduced : ObjectProperty Scheme.{u}) U)
    (g : U.functorOfPoints ⟶ X) :
    ∃! h : U.functorOfPoints ⟶ space.functorOfPoints, h ≫ ι = g

/-- The algebraic-space reduction of a formal algebraic space. -/
abbrev reduction (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : AlgebraicSpace S :=
  R.space

/-- The algebraic-space reduction is the `space` field of `Reduction`. -/
theorem reduction_def (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : reduction X = R.space :=
  sorry

/-- The canonical morphism from the reduction of a formal algebraic space. -/
abbrev reductionι (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : (reduction X).functorOfPoints ⟶ X :=
  R.ι

/-- The reduction morphism is the `ι` field of `Reduction`. -/
theorem reductionι_def (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : reductionι X = R.ι :=
  sorry

/-- The reduction of an algebraic space, viewed as a formal algebraic space, is
the reduced induced algebraic space of Definition 66.12.5. -/
instance instReduction_ofAlgebraicSpace (X : AlgebraicSpace S) :
    Reduction X.functorOfPoints where
  space := AlgebraicSpace.reduction X
  ι := AlgebraicSpace.reductionι X
  isReduced := sorry
  representable := sorry
  isThickening := sorry
  liftUnique := sorry

/-- On an algebraic space, `reduction` recovers `AlgebraicSpace.reduction`. -/
theorem reduction_functorOfPoints (X : AlgebraicSpace S) :
    reduction X.functorOfPoints = AlgebraicSpace.reduction X :=
  sorry

/-- On an algebraic space, `reductionι` recovers `AlgebraicSpace.reductionι`. -/
theorem reductionι_functorOfPoints (X : AlgebraicSpace S) :
    reductionι X.functorOfPoints = AlgebraicSpace.reductionι X :=
  sorry

/-- Lemma 87.12.1: the reduction is reduced, the structure morphism is a
representable thickening, and maps from reduced algebraic spaces factor
uniquely through it. -/
theorem reduction_spec (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] :
    AlgebraicSpace.hasEtaleLocal
        (IsReduced : ObjectProperty Scheme.{u}) (reduction X) ∧
      AlgebraicSpace.representableByAlgebraicSpaces (reductionι X) ∧
        (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ X),
          AlgebraicSpace.IsThickening
            (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom
              R.representable ξ)) ∧
          ∀ {U : AlgebraicSpace S}
            (hU : AlgebraicSpace.hasEtaleLocal
              (IsReduced : ObjectProperty Scheme.{u}) U)
            (g : U.functorOfPoints ⟶ X),
            ∃! h : U.functorOfPoints ⟶ (reduction X).functorOfPoints,
              h ≫ reductionι X = g :=
  sorry


/-- The induced map of algebraic-space reductions along an étale morphism of
formal algebraic spaces, as the unique factor of `reductionι X ≫ f` through
`reductionι Y`. -/
def inducedReductionMap {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y) [Etale f] :
    reduction X ⟶ reduction Y :=
  Classical.choose (RY.liftUnique RX.isReduced (reductionι X ≫ f))

/-- `inducedReductionMap f` factors `reductionι X ≫ f` through `reductionι Y`. -/
theorem inducedReductionMap_spec {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [Etale f] :
    NatTrans.vcomp (inducedReductionMap f) (reductionι Y) =
      NatTrans.vcomp (reductionι X) f :=
  sorry

/-- A morphism of reductions over `f` equals `inducedReductionMap f`. -/
theorem inducedReductionMap_unique {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [Etale f]
    {g : reduction X ⟶ reduction Y}
    (hg : NatTrans.vcomp g (reductionι Y) = NatTrans.vcomp (reductionι X) f) :
    g = inducedReductionMap f :=
  sorry

/-- The fibre product of the reduction of `Y` along an étale morphism `f : X ⟶ Y`
of formal algebraic spaces is an algebraic space. -/
instance instIsAlgebraicSpace_pullback_reductionι
    {X Y : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [Reduction Y] (f : X ⟶ Y) [Etale f] :
    AlgebraicSpace.IsAlgebraicSpace (pullback (reductionι Y) f) :=
  sorry

/-- The reduction of `X` along an étale morphism `f : X ⟶ Y`, realized as the
fibre product `X ×_Y Y_red`. -/
def reductionAlong {X Y : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [Reduction Y] (f : X ⟶ Y) [Etale f] :
    AlgebraicSpace S :=
  AlgebraicSpace.ofIsAlgebraicSpace (pullback (reductionι Y) f)

/-- The functor of points of `reductionAlong f` is the fibre product of
`reductionι Y` and `f`. -/
theorem reductionAlong_functorOfPoints {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    (reductionAlong f).functorOfPoints = pullback (reductionι Y) f :=
  sorry

/-- The structure morphism `X_red ⟶ X` of the étale-case reduction, as the
second projection of `X ×_Y Y_red`. -/
def reductionιAlong {X Y : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [Reduction Y] (f : X ⟶ Y) [Etale f] :
    (reductionAlong f).functorOfPoints ⟶ X :=
  pullback.snd (reductionι Y) f

/-- `reductionιAlong f` is the second projection of the fibre product. -/
theorem reductionιAlong_snd {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    reductionιAlong f = pullback.snd (reductionι Y) f :=
  sorry

/-- The induced morphism of reductions along an étale morphism of formal
algebraic spaces, as the first projection of `X ×_Y Y_red`. -/
def reductionMap {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] : reductionAlong f ⟶ reduction Y :=
  pullback.fst (reductionι Y) f

/-- `reductionMap f` is the first projection of the fibre product. -/
theorem reductionMap_fst {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    reductionMap f = pullback.fst (reductionι Y) f :=
  sorry

/-- The source square `X_red = X ×_Y Y_red` for an étale morphism of formal
algebraic spaces. -/
theorem reductionAlong_isPullback {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    IsPullback (reductionιAlong f) (reductionMap f) f (reductionι Y) :=
  sorry

/-- The fibre product `X ×_Y Y_red` is reduced. -/
theorem reductionAlong_isReduced {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    AlgebraicSpace.hasEtaleLocal
      (IsReduced : ObjectProperty Scheme.{u}) (reductionAlong f) :=
  sorry

/-- The projection `X ×_Y Y_red ⟶ X` is representable by algebraic spaces. -/
theorem reductionιAlong_representable {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    AlgebraicSpace.representableByAlgebraicSpaces (reductionιAlong f) :=
  sorry

/-- Yoneda pullbacks of `reductionιAlong f` are thickenings. -/
theorem reductionιAlong_isThickening {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] {U : Over S} (ξ : yoneda.obj U ⟶ X)
    (h : AlgebraicSpace.representableByAlgebraicSpaces (reductionιAlong f)) :
    AlgebraicSpace.IsThickening
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom h ξ) :=
  sorry

/-- The Lemma 87.12.1 reduction of `X` is isomorphic to the fibre product
`X ×_Y Y_red` over `X`, when `f` is étale. -/
def reductionIsoAlong {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y) [Etale f] :
    reduction X ≅ reductionAlong f where
  hom :=
    pullback.lift (C := (Over S)ᵒᵖ ⥤ Type u) (f := reductionι Y) (g := f)
      (inducedReductionMap f) (reductionι X)
      (Classical.choose_spec
        (RY.liftUnique RX.isReduced (reductionι X ≫ f))).1
  inv :=
    Classical.choose
      (RX.liftUnique (reductionAlong_isReduced f) (reductionιAlong f))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward triangle: `reductionIsoAlong f` is a morphism over `X`. -/
theorem reductionIsoAlong_hom_comp_ι {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [Etale f] :
    NatTrans.vcomp (reductionIsoAlong f).hom (reductionιAlong f) =
      reductionι X :=
  sorry

/-- The reverse triangle: the inverse of `reductionIsoAlong f` is a morphism
over `X`. -/
theorem reductionIsoAlong_inv_comp_ι {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [Etale f] :
    NatTrans.vcomp (reductionIsoAlong f).inv (reductionι X) =
      reductionιAlong f :=
  sorry

/-- The induced map of reductions is the composite of `reductionIsoAlong f`
with the pullback projection `reductionMap f`. -/
theorem inducedReductionMap_eq_comp {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [Etale f] :
    inducedReductionMap f = (reductionIsoAlong f).hom ≫ reductionMap f :=
  sorry

/-- An étale morphism of formal algebraic spaces that is representable by
algebraic spaces induces an étale morphism of algebraic-space reductions. -/
instance instEtale_reductionMap {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] : AlgebraicSpace.Etale (reductionMap f) :=
  sorry

/-- `inducedReductionMap f` is étale, by transporting `instEtale_reductionMap`
along `reductionIsoAlong`. -/
instance instEtale_inducedReductionMap {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [Etale f] :
    AlgebraicSpace.Etale (inducedReductionMap f) :=
  sorry

/-- The étale-case reduction is the fibre product of `Y_red` along `f`, it is
reduced, the projection to `X` is a representable thickening, the induced map
of reductions is étale, and the resulting square is cartesian. -/
theorem reductionAlong_spec {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    (reductionAlong f).functorOfPoints = pullback (reductionι Y) f ∧
      AlgebraicSpace.hasEtaleLocal
          (IsReduced : ObjectProperty Scheme.{u}) (reductionAlong f) ∧
        AlgebraicSpace.representableByAlgebraicSpaces (reductionιAlong f) ∧
          AlgebraicSpace.Etale (reductionMap f) ∧
            IsPullback (reductionιAlong f) (reductionMap f) f
              (reductionι Y) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
