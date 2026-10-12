/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FinitePresentation
public import Mathlib.CategoryTheory.Presentable.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/- Lemma 56.6.1: for a quasi-compact and quasi-separated scheme, a
quasi-coherent module is categorically compact in `QCoh` if and only if its
underlying module sheaf is of finite presentation. -/
@[stacks 0GPE] #check
  (AlgebraicGeometry.Scheme.QCoh.isFinitelyPresentable_iff_isFinitePresentation :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (F : Scheme.QCoh X),
      CategoryTheory.IsFinitelyPresentable.{u} F ↔ F.obj.IsFinitePresentation)

end AlgebraicGeometry.Scheme.QCoh
