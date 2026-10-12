/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.FinitePresentation
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.22.10: on a quasi-compact quasi-separated scheme, every quasi-coherent algebra
sheaf is a filtered colimit, among all algebra sheaves, of quasi-coherent finitely presentable
algebra sheaves. -/
@[stacks 05JS] #check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder.finitelyPresentable_ind :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (A : X.QcAlgebraUnder),
      (AlgebraicGeometry.Scheme.QcAlgebraUnder.finitelyPresentableProperty X).ind.{u} A.obj)
