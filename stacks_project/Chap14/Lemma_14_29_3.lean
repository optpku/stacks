/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Homotopy
import StacksCheckRecall

/-!
@stack 01A4
-/

@[expose] public section

open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a b : U ⟶ V}

/- Lemma 14.29.3 (01A4): a prescribed chain homotopy between `N(a)` and `N(b)` is induced by
a directed simplicial homotopy from `a` to `b`, with equality of the canonical normalized-Moore
homotopies. -/
@[stacks 01A4]
#check (Homotopy.normalizedMoore.exists_eq
  (A := A) (a := a) (b := b) :
  ∀ N : _root_.Homotopy
      ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b),
    ∃ H : Homotopy a b, N = H.normalizedMoore)

/- The reusable canonical formulation is surjectivity of the normalized-Moore homotopy map. -/
#check (Homotopy.normalizedMoore.surjective
  (A := A) (a := a) (b := b) :
  Function.Surjective
    (Homotopy.normalizedMoore (A := A) (a := a) (b := b)))

end CategoryTheory.SimplicialObject
