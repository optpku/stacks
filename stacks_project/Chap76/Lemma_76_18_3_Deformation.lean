module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap74.Lemma_74_11_29_Instances
public import stacks_project.Chap76.Definition_76_9_1_FiniteOrder
public import stacks_project.Chap76.Lemma_76_9_2_Thickening

/-!
# Morphism properties in finite-order deformations of algebraic spaces

This file records invariance of morphism properties of algebraic spaces in
cartesian diagrams of thickenings over a finite-order thickening of the base,
assuming the ambient source is flat over the thickened base.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite locally free morphism `f : X ⟶ Y` of algebraic spaces over `S` has
rank or degree `d` if `f_* 𝒪_X` is finite locally free of rank `d`. -/
class FiniteLocallyFreeOfRank {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) : Prop extends FiniteLocallyFree f where
  /-- The pushforward structure sheaf has rank `d`. -/
  pushforward_isFiniteLocallyFreeOfRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank d (Hom.pushforwardStructureModule f)

/-- A morphism of algebraic spaces is finite locally free of rank `d` if and
only if it is finite locally free and its pushforward structure sheaf has rank
`d`. -/
theorem finiteLocallyFreeOfRank_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) :
    FiniteLocallyFreeOfRank f d ↔
      FiniteLocallyFree f ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank d
          (Hom.pushforwardStructureModule f) :=
  sorry

namespace FiniteLocallyFreeOfRank

/-- The identity morphism of an algebraic space is finite locally free of rank
`1`. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    FiniteLocallyFreeOfRank (𝟙 X) 1 :=
  sorry

/-- A finite locally free morphism of rank `d` is finite locally free and has
pushforward structure sheaf of rank `d`. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ)
    [FiniteLocallyFreeOfRank f d] :
    FiniteLocallyFree f ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank d
        (Hom.pushforwardStructureModule f) :=
  sorry

end FiniteLocallyFreeOfRank

namespace IsFiniteOrderThickening

variable {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
variable {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}
variable {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
variable [thickeningX : IsThickening iX] [thickeningY : IsThickening iY]
variable [finiteOrderB : IsFiniteOrderThickening iB] [flatX' : Flat pX']
variable (sq : CommSq f iX iY f')
variable (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
variable (pullbackX : IsPullback pX iX iB pX') (pullbackY : IsPullback pY iY iB pY')

include thickeningX thickeningY finiteOrderB flatX'
include sq triangle triangle' pullbackX pullbackY

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is representable if and only if
the ambient morphism is representable. -/
theorem relativelyRepresentable_iff :
    yoneda.relativelyRepresentable f ↔ yoneda.relativelyRepresentable f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is flat if and only if the
ambient morphism is flat. -/
theorem flat_iff : Flat f ↔ Flat f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is an isomorphism if and only
if the ambient morphism is an isomorphism. -/
theorem isIso_iff : IsIso f ↔ IsIso f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is an open immersion if and
only if the ambient morphism is an open immersion. -/
theorem isOpenImmersion_iff : IsOpenImmersion f ↔ IsOpenImmersion f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is quasi-compact if and only if
the ambient morphism is quasi-compact. -/
theorem quasiCompact_iff : QuasiCompact f ↔ QuasiCompact f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is universally closed if and
only if the ambient morphism is universally closed. -/
theorem universallyClosed_iff : UniversallyClosed f ↔ UniversallyClosed f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is separated if and only if the
ambient morphism is separated. -/
theorem separated_iff : Separated f ↔ Separated f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is quasi-separated if and only
if the ambient morphism is quasi-separated. -/
theorem quasiSeparated_iff : QuasiSeparated f ↔ QuasiSeparated f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is a monomorphism if and only
if the ambient morphism is a monomorphism. -/
theorem mono_iff : Mono f ↔ Mono f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is surjective if and only if
the ambient morphism is surjective. -/
theorem surjective_iff : Surjective f ↔ Surjective f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is universally injective if and
only if the ambient morphism is universally injective. -/
theorem universallyInjective_iff :
    UniversallyInjective f ↔ UniversallyInjective f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is affine if and only if the
ambient morphism is affine. -/
theorem affine_iff : Affine f ↔ Affine f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is locally of finite type if
and only if the ambient morphism is locally of finite type. -/
theorem locallyOfFiniteType_iff :
    LocallyOfFiniteType f ↔ LocallyOfFiniteType f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is locally quasi-finite if and
only if the ambient morphism is locally quasi-finite. -/
theorem locallyQuasiFinite_iff : LocallyQuasiFinite f ↔ LocallyQuasiFinite f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is locally of finite
presentation if and only if the ambient morphism is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_iff :
    LocallyOfFinitePresentation f ↔ LocallyOfFinitePresentation f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is locally of finite type of
relative dimension `d` if and only if the ambient morphism is locally of finite
type of relative dimension `d`. -/
theorem relativeDimension_iff (d : ℕ) :
    (LocallyOfFiniteType f ∧ RelativeDimension f d) ↔
      (LocallyOfFiniteType f' ∧ RelativeDimension f' d) := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is universally open if and only
if the ambient morphism is universally open. -/
theorem universallyOpen_iff : UniversallyOpen f ↔ UniversallyOpen f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is syntomic if and only if the
ambient morphism is syntomic. -/
theorem syntomic_iff : Syntomic f ↔ Syntomic f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is smooth if and only if the
ambient morphism is smooth. -/
theorem smooth_iff : Smooth f ↔ Smooth f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is unramified if and only if
the ambient morphism is unramified. -/
theorem unramified_iff : Unramified f ↔ Unramified f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is étale if and only if the
ambient morphism is étale. -/
theorem etale_iff : Etale f ↔ Etale f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is proper if and only if the
ambient morphism is proper. -/
theorem proper_iff : Proper f ↔ Proper f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is integral if and only if the
ambient morphism is integral. -/
theorem isIntegralHom_iff : IsIntegralHom f ↔ IsIntegralHom f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is finite if and only if the
ambient morphism is finite. -/
theorem isFinite_iff : IsFinite f ↔ IsFinite f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is finite locally free if and
only if the ambient morphism is finite locally free. -/
theorem finiteLocallyFree_iff : FiniteLocallyFree f ↔ FiniteLocallyFree f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, the closed-fiber morphism is finite locally free of rank
`d` if and only if the ambient morphism is finite locally free of rank `d`. -/
theorem finiteLocallyFreeOfRank_iff (d : ℕ) :
    FiniteLocallyFreeOfRank f d ↔ FiniteLocallyFreeOfRank f' d := sorry

end IsFiniteOrderThickening

end AlgebraicGeometry.AlgebraicSpace
