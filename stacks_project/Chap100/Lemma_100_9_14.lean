module

import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Union
import StacksCheckRecall

/-!
# Union of open substacks

A family of open substacks of an algebraic stack has a union open substack
which they cover.
-/

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 100.9.14: Any family of open substacks of an algebraic stack has an
open union in which the members are open substacks and jointly cover. -/
@[stacks 05UQ] #check (AlgebraicGeometry.AlgebraicStack.Substack.exists_iUnion :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {I : Type v}
    (P : I → ObjectProperty X.total) (hP : ∀ i, Substack.IsOpen X (P i)),
    ∃ Q : ObjectProperty X.total, Substack.IsOpen X Q ∧ (∀ i, P i ≤ Q) ∧
      (∀ (hQ : Functor.IsFibered.InGroupoids (Q.ι ⋙ X.p)) (i : I),
        Substack.IsOpen (Substack.category X Q hQ) (fun z ↦ P i z.obj)) ∧
      (∀ x : X.total, Q x ↔ ∀ t : (X.p.obj x).left,
        ∃ (i : I) (y : X.total) (f : y ⟶ x) (s : (X.p.obj y).left),
          P i y ∧ (X.p.map f).left.base s = t))

end AlgebraicGeometry.AlgebraicStack
