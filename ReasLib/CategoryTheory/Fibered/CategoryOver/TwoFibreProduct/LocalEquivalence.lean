/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Fibered.Closure
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local equivalences and two-fibre products of fibred categories

The heterogeneous closure theorem is owned by
`BasedCategory.PseudoPullback.cartesianMap.isLocalEquivalence`. This leaf retains its
same-universe bicategorical specialization for `LocallyInduced.TwoFibreProduct.map`, independently
of stack hypotheses.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace FiberedCategoryOver.TwoFibreProduct

variable
  {X₁ Y₁ S₁ X₂ Y₂ S₂ :
    FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C}
  {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
  {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

namespace map

/-- The fixed-universe bicategorical specialization of heterogeneous pseudo-pullback
local-equivalence closure. -/
@[stacks 04Y1 "fixed-universe two-fibre-product local-equivalence closure"]
theorem isLocalEquivalence
    (ψ : CospanTransform F₁ G₁ F₂ G₂)
    (hleft : Hom.IsLocalEquivalence J ψ.left)
    (hright : Hom.IsLocalEquivalence J ψ.right)
    (hbase : Hom.IsLocalEquivalence J ψ.base) :
    Hom.IsLocalEquivalence J (map ψ) := sorry

end map

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
