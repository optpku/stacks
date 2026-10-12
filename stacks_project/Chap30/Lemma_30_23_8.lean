/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.AssociatedGraded
import StacksCheckRecall

/- Lemma 30.23.8: for a Noetherian scheme `X`, a quasi-coherent ideal sheaf `I`, and
`F ∈ Coh(X, I)`, the graded quasi-coherent module `⨁ n, ker(F_{n+1} ⟶ F_n)` is finite type
over `⨁ n, I^n / I^(n + 1)`. The canonical owner is the scheme-level associated-graded theorem on
transition kernels. -/
@[stacks 087Z] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.transitionKernelDirectSum_finite :
    ∀ {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsNoetherian X]
      (I : X.IdealSheafData) (F : AlgebraicGeometry.Scheme.CoherentFormalModules X I),
      AlgebraicGeometry.Scheme.CoherentFormalModules.TransitionKernelDirectSum.IsFiniteType I F)
