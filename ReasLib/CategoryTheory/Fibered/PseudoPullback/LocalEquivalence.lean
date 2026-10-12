/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cartesian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local equivalences and heterogeneous pseudo-pullbacks

This module records the local-equivalence closure of the explicit pseudo-pullback map.  The
map data remain owned by `BasedCategory.PseudoPullback.map`; the cartesian bundle is owned by
`BasedCategory.PseudoPullback.cartesianMap`.
-/

@[expose] public section

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
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
variable [X₂.p.IsFibered] [Y₂.p.IsFibered] [S₂.p.IsFibered]

namespace BasedCategory.PseudoPullback.cartesianMap

/-- A cospan transformation whose three cartesian components are heterogeneous local
equivalences induces a local equivalence between the explicit pseudo-pullbacks. -/
@[stacks 04Y1 "pseudo-pullback closure under local equivalences"]
theorem isLocalEquivalence
    (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂)
    (hleft : CartesianBasedFunctor.IsLocalEquivalence J ψ.left)
    (hright : CartesianBasedFunctor.IsLocalEquivalence J ψ.right)
    (hbase : CartesianBasedFunctor.IsLocalEquivalence J ψ.base) :
    CartesianBasedFunctor.IsLocalEquivalence J
      (BasedCategory.PseudoPullback.cartesianMap ψ) := sorry

end BasedCategory.PseudoPullback.cartesianMap

end CategoryTheory
