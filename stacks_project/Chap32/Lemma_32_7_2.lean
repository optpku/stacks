/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.RelativeFinitePresentationApproximation
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 32.7.2: every morphism from a quasi-compact, quasi-separated scheme to a
quasi-separated scheme is a directed limit of schemes of finite presentation over the base,
with affine transition morphisms over the base. -/
@[stacks 09MV] #check
  (AlgebraicGeometry.Scheme.Limit.exists_relativeFinitePresentationApproximation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X]
      [QuasiSeparatedSpace S],
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ Scheme.{u})
        (π : (Functor.const (OrderDual I)).obj X ⟶ D)
        (σ : (j : I) → D.obj j ⟶ S),
        AlgebraicGeometry.Scheme.Limit.IsRelativeFinitePresentationApproximation f D π σ)
