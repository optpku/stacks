/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Cospan.PrecompLift
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct
public import ReasLib.CategoryTheory.Fibered.Stack.PseudoPullback.Closure
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Criteria
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stackifications and two-fibre products

This file separates three layers: `CartesianCospanTransform.ofPrecompLifts` constructs compatible
target legs from explicit quasi-inverses, `BasedCategory.PseudoPullback.cartesianMap` induces the
heterogeneous map, and the theorems below provide local-equivalence closure and source-faithful
existence. The fixed-universe bicategorical map remains owned by
`FiberedCategoryOver.TwoFibreProduct.map`.
-/

@[expose] public section

universe u v w vB
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

namespace CategoryTheory

open Bicategory
open scoped Bicategory CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace BasedCategory.PseudoPullback.cartesianMap

variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {F₁ : CartesianBasedFunctor X₁.p S₁.p}
variable {G₁ : CartesianBasedFunctor Y₁.p S₁.p}
variable {F₂ : CartesianBasedFunctor X₂.p S₂.p}
variable {G₂ : CartesianBasedFunctor Y₂.p S₂.p}
variable [X₁.p.IsFibered] [Y₁.p.IsFibered] [S₁.p.IsFibered]

/-- A heterogeneous componentwise local equivalence induces a stackification between explicit
pseudo-pullbacks when the two target endpoints are stacks and their common target is a prestack.
These are exactly the target hypotheses needed for pseudo-pullback stack closure. -/
@[stacks 04Y1 "heterogeneous pseudo-pullback stackification from local equivalences"]
theorem isStackification_of_isLocalEquivalence
    (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂)
    [IsStack.OnSite J X₂.p] [IsStack.OnSite J Y₂.p]
    [IsPrestack.OnSite J S₂.p]
    (hleft : CartesianBasedFunctor.IsLocalEquivalence J ψ.left)
    (hright : CartesianBasedFunctor.IsLocalEquivalence J ψ.right)
    (hbase : CartesianBasedFunctor.IsLocalEquivalence J ψ.base) :
    CartesianBasedFunctor.IsStackification J
      (BasedCategory.PseudoPullback.cartesianMap ψ) := sorry

variable [X₂.p.IsFibered] [Y₂.p.IsFibered] [S₂.p.IsFibered]

/-- A heterogeneous componentwise stackification induces a stackification between the explicit
pseudo-pullbacks. The induced map is the canonical componentwise map, not a chosen lift. -/
@[stacks 04Y1 "heterogeneous pseudo-pullback stackification closure"]
theorem isStackification
    (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂)
    (hleft : CartesianBasedFunctor.IsStackification J ψ.left)
    (hright : CartesianBasedFunctor.IsStackification J ψ.right)
    (hbase : CartesianBasedFunctor.IsStackification J ψ.base) :
    CartesianBasedFunctor.IsStackification J
      (BasedCategory.PseudoPullback.cartesianMap ψ) := sorry

/-- Given stackifications of the three objects in a cospan, there are compatible target legs
whose componentwise map of pseudo-pullbacks is a stackification. This is the source-faithful
existence form; consumers requiring stable data should use `ofPrecompLifts` with explicit
quasi-inverses. -/
@[stacks 04Y1 "source-faithful heterogeneous existence form"]
theorem exists_of_stackifications
    (iX : CartesianBasedFunctor X₁.p X₂.p)
    (iY : CartesianBasedFunctor Y₁.p Y₂.p)
    (iS : CartesianBasedFunctor S₁.p S₂.p)
    (hX : CartesianBasedFunctor.IsStackification J iX)
    (hY : CartesianBasedFunctor.IsStackification J iY)
    (hS : CartesianBasedFunctor.IsStackification J iS) :
    ∃ F₂ : CartesianBasedFunctor X₂.p S₂.p,
      ∃ G₂ : CartesianBasedFunctor Y₂.p S₂.p,
        ∃ ψ : CartesianCospanTransform F₁ G₁ F₂ G₂,
          ψ.left = iX ∧ ψ.right = iY ∧ ψ.base = iS ∧
            CartesianBasedFunctor.IsStackification J
              (BasedCategory.PseudoPullback.cartesianMap ψ) := sorry

attribute [stacks 04Y2 "two-fibre-products preserve stackifications"]
  exists_of_stackifications

/-- Explicit quasi-inverses to precomposition construct the target cospan and its comparison
isomorphisms. If the three prescribed endpoint maps are stackifications, the resulting
componentwise map of pseudo-pullbacks is a stackification. -/
@[stacks 04Y1 "explicit precomposition-lift form"]
theorem isStackification_ofPrecompLifts
    {iX : CartesianBasedFunctor X₁.p X₂.p}
    {iY : CartesianBasedFunctor Y₁.p Y₂.p}
    (iS : CartesianBasedFunctor S₁.p S₂.p)
    (qX : Functor.QuasiInverse (CartesianBasedFunctor.precomp S₂.p iX))
    (qY : Functor.QuasiInverse (CartesianBasedFunctor.precomp S₂.p iY))
    (hX : CartesianBasedFunctor.IsStackification J iX)
    (hY : CartesianBasedFunctor.IsStackification J iY)
    (hS : CartesianBasedFunctor.IsStackification J iS) :
    CartesianBasedFunctor.IsStackification J
      (BasedCategory.PseudoPullback.cartesianMap
        (CartesianCospanTransform.ofPrecompLifts F₁ G₁ iS qX qY)) := sorry

end BasedCategory.PseudoPullback.cartesianMap

namespace FiberedCategoryOver.TwoFibreProduct

variable
  {X₁ Y₁ S₁ X₂ Y₂ S₂ :
    FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C}
  {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
  {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

namespace map

/-- A componentwise local equivalence induces a stackification between explicit two-fibre
products when its two target ends are stacks and their common target is a prestack. The weaker
prestack hypothesis on `S₂` is exactly what ambient two-fibre-product stack closure requires. -/
@[stacks 04Y1 "fixed-universe two-fibre-product stackification from local equivalences"]
theorem isStackification_of_isLocalEquivalence
    (ψ : CospanTransform F₁ G₁ F₂ G₂)
    (hleft : Hom.IsLocalEquivalence J ψ.left)
    (hright : Hom.IsLocalEquivalence J ψ.right)
    (hbase : Hom.IsLocalEquivalence J ψ.base)
    [IsStack.OnSite J X₂.p] [IsStack.OnSite J Y₂.p]
    [IsPrestack.OnSite J S₂.p] :
    Hom.IsStackification J (FiberedCategoryOver.TwoFibreProduct.map ψ) := sorry

/-- A componentwise stackification cospan map is a stackification. The component
stackifications supply the local equivalences and target conditions required by
`isStackification_of_isLocalEquivalence`. -/
@[stacks 04Y1 "fixed-universe two-fibre-product stackification closure"]
theorem isStackification
    (ψ : CospanTransform F₁ G₁ F₂ G₂)
    (hleft : Hom.IsStackification J ψ.left)
    (hright : Hom.IsStackification J ψ.right)
    (hbase : Hom.IsStackification J ψ.base) :
    Hom.IsStackification J (FiberedCategoryOver.TwoFibreProduct.map ψ) := sorry

/-- For three stackification morphisms in `FiberedCategoryOver`, compatible target legs exist
and their componentwise two-fibre-product map is a stackification. -/
@[stacks 04Y1 "fixed-universe existence form"]
theorem exists_of_stackifications
    (iX : X₁ ⟶ X₂) (iY : Y₁ ⟶ Y₂) (iS : S₁ ⟶ S₂)
    (hX : Hom.IsStackification J iX)
    (hY : Hom.IsStackification J iY)
    (hS : Hom.IsStackification J iS) :
    ∃ F₂ : X₂ ⟶ S₂, ∃ G₂ : Y₂ ⟶ S₂,
      ∃ ψ : CospanTransform F₁ G₁ F₂ G₂,
        ψ.left = iX ∧ ψ.right = iY ∧ ψ.base = iS ∧
          Hom.IsStackification J (FiberedCategoryOver.TwoFibreProduct.map ψ) := sorry

end map

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
