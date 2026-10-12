/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.BaseChange
import StacksCheckRecall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ j, CompactSpace (D.obj j)]
variable [∀ j, QuasiSeparatedSpace (D.obj j)]
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]
variable (i : I) {T : Scheme.{u}} (t : T ⟶ D.obj i) [CompactSpace T]

/- Lemma 32.4.9: in Situation 32.4.5, if the base change of a quasi-compact
scheme to the limit is empty, then all sufficiently late base changes are empty. -/
@[stacks 05F3] #check
  (AlgebraicGeometry.Scheme.exists_eventually_isEmpty_baseChangeOverDiagram D c hc i t :
    IsEmpty (Scheme.baseChangeOverCone D c i t).pt →
      ∃ (i₀ : I) (hii₀ : i ≤ i₀), ∀ ⦃i' : I⦄, (hi₀i' : i₀ ≤ i') →
        IsEmpty ((Scheme.baseChangeOverDiagram D i t).obj
          (Over.mk (homOfLE ((le_trans hii₀ hi₀i' : i ≤ i') :
            OrderDual.toDual i' ≤ OrderDual.toDual i)))))

end

end AlgebraicGeometry
