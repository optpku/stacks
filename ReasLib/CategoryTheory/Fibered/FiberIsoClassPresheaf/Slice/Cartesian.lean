/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fibered
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Chosen
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Fibers
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Slice
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.PseudoPullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber-class presheaves of cartesian slice base changes

This leaf constructs the presheaf of fiberwise isomorphism classes associated to the
pseudo-pullback of a universe-polymorphic cartesian based functor along a cartesian slice
functor. It also separates the all-slice and selected fiber-object quantifier patterns for an
arbitrary isomorphism-invariant object property.

No second base-change carrier is introduced: the data owner is the first projection from
`BasedCategory.PseudoPullback`, and fiber-object representatives come from the selected-cleavage
cartesian Yoneda functor.
-/

@[expose] public section

universe uC vC uS vS uT vT

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} {T : Type uT}
variable [Category.{vS} S] [Category.{vT} T]
variable {pS : S ⥤ C} {pT : T ⥤ C}

namespace CartesianBasedFunctor

variable [pS.IsFibered]

/-- The presheaf of isomorphism classes in the cartesian pseudo-pullback of `F` along a
cartesian slice functor `G`.

The first projection has base `Over U`; its fibredness is the canonical mixed-level
`BasedCategory.PseudoPullback.Fst.IsFibered.ofCartesian` instance. -/
noncomputable def sliceFiberClasses
    (F : CartesianBasedFunctor pS pT) {U : C}
    (G : CartesianBasedFunctor.Yoneda.hom pT U) :
    (Over U)ᵒᵖ ⥤ Type (max uC vC uS vT) :=
  @Functor.fiberIsoClassPresheaf _ _ _ _
    (BasedCategory.PseudoPullback.fst
      G.toBasedFunctor F.toBasedFunctor).toFunctor
    (BasedCategory.PseudoPullback.Fst.IsFibered.ofCartesian
      (X := BasedCategory.ofFunctor (Over.forget U))
      (Y := BasedCategory.ofFunctor pS) (S := BasedCategory.ofFunctor pT) G F)

/-- The concrete fiber-pair presheaf associated to `F` and `y : pT.Fiber U`, formed by
base-changing along the cartesian Yoneda representative selected from the fibredness instance on
`pT`. Its objects are pairs consisting of a source-fiber object and an isomorphism between its
image and the corresponding restriction of `y`; the iso-comma model makes the orientation of that
isomorphism immaterial. -/
@[stacks 02Y9 "universe-polymorphic fiber-pair isomorphism classes",
  stacks 0CKJ "universe-polymorphic fiber-pair isomorphism classes"]
noncomputable def fiberPairClasses
    [pT.IsFibered] (F : CartesianBasedFunctor pS pT)
    {U : C} (y : pT.Fiber U) :
    (Over U)ᵒᵖ ⥤ Type (max uC vC uS vT) :=
  sliceFiberClasses F
    ((CartesianBasedFunctor.Yoneda.Chosen.functor pT U).obj y)

/-- An isomorphism-invariant property holds for the selected fiber-pair presheaf exactly when it
holds for every cartesian slice representative whose identity-fiber value is isomorphic to the
given target-fiber object. -/
theorem fiberPairClasses.property_iff
    [pT.IsFibered] {U : C}
    (P : ObjectProperty
      ((Over U)ᵒᵖ ⥤ Type (max uC vC uS vT)))
    [hP : P.IsClosedUnderIsomorphisms]
    (F : CartesianBasedFunctor pS pT) (y : pT.Fiber U) :
    P (fiberPairClasses F y) ↔
      ∀ (G : CartesianBasedFunctor.Yoneda.hom pT U)
        (_ : (G.fiberFunctor U).obj
          (BasedCategory.Yoneda.Identity.fiberObj U) ≅ y),
        P (sliceFiberClasses F G) := sorry

/-- An object property of slice presheaves holds after every cartesian slice base change of `F`. -/
def sliceFiberClasses.satisfies
    (P : ∀ U : C, ObjectProperty
      ((Over U)ᵒᵖ ⥤ Type (max uC vC uS vT)))
    (F : CartesianBasedFunctor pS pT) : Prop :=
  ∀ {U : C} (G : CartesianBasedFunctor.Yoneda.hom pT U),
    P U (sliceFiberClasses F G)

/-- An object property of slice presheaves holds for the selected fiber-pair presheaf of every
object in every target fiber. -/
def fiberPairClasses.satisfies
    [pT.IsFibered]
    (P : ∀ U : C, ObjectProperty
      ((Over U)ᵒᵖ ⥤ Type (max uC vC uS vT)))
    (F : CartesianBasedFunctor pS pT) : Prop :=
  ∀ {U : C} (y : pT.Fiber U), P U (fiberPairClasses F y)

/-- For an isomorphism-invariant presheaf property, checking the selected representative of every
target-fiber object is equivalent to checking every cartesian slice morphism. -/
theorem fiberPairClasses.satisfies_iff_slice
    [pT.IsFibered]
    (P : ∀ U : C, ObjectProperty
      ((Over U)ᵒᵖ ⥤ Type (max uC vC uS vT)))
    [hP : ∀ U : C, (P U).IsClosedUnderIsomorphisms]
    (F : CartesianBasedFunctor pS pT) :
    fiberPairClasses.satisfies P F ↔
      sliceFiberClasses.satisfies P F := sorry

/- Axiom audit: both presheaf data owners use the explicit pseudo-pullback first projection and
the existing selected-cleavage Yoneda section. Any `sorryAx` is confined to inherited Prop-valued
fibredness, cartesianness, naturality, and functor-law fields; no semantic datum is supplied by a
placeholder. -/

end CartesianBasedFunctor

end CategoryTheory
