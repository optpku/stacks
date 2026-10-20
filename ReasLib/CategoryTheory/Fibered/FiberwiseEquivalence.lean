/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.FiberwiseEquivalence
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber

/-!
# Fiberwise criteria for morphisms of fibred categories

A cartesian functor between fibred categories is faithful, fully faithful, or an equivalence over
the base precisely when its restrictions to the fibers have the corresponding property.  These
criteria are intrinsic to fibred categories; no groupoid hypothesis and no choice of cleavage is
needed.

The total and fiberwise criteria are kept atomic so applications can use only the strength they
need. In a fixed owner bicategory, the primary equivalence conclusion is an actual
`Bicategory.Equivalence` whose forward `1`-morphism is the supplied morphism. The
`BasedFunctor.IsEquivalence` conclusion is the property/typeclass bridge for a fixed morphism
whose source and target must cross owner universes.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver

variable {X Y : FiberedCategoryOver C}
variable (F : X ⟶ Y)

/-- A morphism of fibred categories over `C` is faithful exactly when every induced fiber functor
is faithful.

Proof strategy: the forward implication is restriction to a fiber. Conversely, for a morphism
over `f : U ⟶ V`, choose a strongly cartesian lift `f⁎y ⟶ y`; its universal property identifies
morphisms `x ⟶ y` over `f` with vertical morphisms `x ⟶ f⁎y` in the fiber over `U`. The morphism
`F` preserves the chosen strongly cartesian arrow, so fiberwise injectivity transports through
these two identifications. -/
theorem faithful_iff_fiberwise :
    (toBasedFunctor F).Faithful ↔ ∀ U : C, (fiberFunctor F U).Faithful := sorry

/-- A morphism of fibred categories over `C` is fully faithful exactly when every induced fiber
functor is fully faithful.

Proof strategy: use the same strongly-cartesian factorization as in
`faithful_iff_fiberwise`. It turns every hom-set over an arbitrary base arrow into a vertical
hom-set in one fiber, compatibly with `F`; fiberwise bijectivity therefore gives global
bijectivity. Restriction proves the reverse direction. -/
theorem fullyFaithful_iff_fiberwise :
    Nonempty (toBasedFunctor F).FullyFaithful ↔
      ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful := sorry

/-- Fiberwise equivalences of a cartesian functor between fibred categories assemble to a
bicategorical equivalence whose forward `1`-morphism is the supplied functor.

Fiberwise full faithfulness gives full faithfulness on the total categories via
`fullyFaithful_iff_fiberwise`; fiberwise essential surjectivity chooses every target object inside
its actual fiber, so the resulting objectwise comparison is vertical and the quasi-inverse can be
made strict over `C`.

Proof strategy: obtain global full faithfulness from `fullyFaithful_iff_fiberwise`; choose for each
`y` a preimage in the fiber over `Y.p.obj y`; use the chosen vertical isomorphisms and the canonical
fully-faithful lift to build a based quasi-inverse, then package the vertical unit and counit with
`Bicategory.Equivalence.mkOfAdjointifyCounit`. -/
theorem exists_equivalence_of_fiberwise
    (hFiber : ∀ U : C, (fiberFunctor F U).IsEquivalence) :
    ∃ e : X ≌ Y, e.hom = F := sorry

/-- Heterogeneous compatibility form of `exists_equivalence_of_fiberwise`, exposing only the
underlying based functor and its quasi-inverse property. Same-owner consumers should use the
bicategorical theorem above. -/
theorem basedFunctorIsEquivalence_of_fiberwise
    (hFiber : ∀ U : C, (fiberFunctor F U).IsEquivalence) :
    BasedFunctor.IsEquivalence (toBasedFunctor F) := sorry

end FiberedCategoryOver

end CategoryTheory
