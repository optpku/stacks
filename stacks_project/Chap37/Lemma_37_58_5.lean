/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/- Lemma 37.58.5: relative finite presentation of a quasi-coherent scheme module is
preserved by arbitrary scheme base change. -/
@[stacks 09TA]
#check
  (AlgebraicGeometry.Scheme.Modules.isFinitePresentationOver_pullback_fst :
    ∀ {S X S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules) [F.IsQuasicoherent], F.IsFinitePresentationOver f →
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsFinitePresentationOver
          (pullback.snd f g))
