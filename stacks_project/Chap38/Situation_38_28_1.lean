/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.FormalSystem

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

/- Situation 38.28.1: `A_lim` realizes `A = lim Aₙ`, the transition maps of `A`
are surjective with locally nilpotent kernels, and `f : X ⟶ Spec A` is separated
and of finite presentation. Each `Xn n` is the pullback of `X` to
`Spec (A.obj (Opposite.op n))` and
is a closed subscheme of `X`. The finitely presented modules `ℱ n` are flat and
have proper support over `Spec (A.obj (Opposite.op n))`; pulling back `ℱ (n + 1)`
to `Xn n` along `i n` gives the isomorphism `φ n` to `ℱ n`. -/
@[stacks 0CTC] #check
  (AlgebraicGeometry.Scheme.Modules.ProperFlatFormalSystem.of :
    (A : SequentialInverseSystem CommRingCat.{u}) →
    (A_lim : LimitCone A) →
    A.Surjective →
    A.KernelLocallyNilpotent →
    (X : Scheme.{u}) →
    (f : X ⟶ Spec A_lim.cone.pt) →
    [IsSeparated f] →
    [Scheme.Hom.FinitePresentation f] →
    (Xn : ℕ → Scheme.{u}) →
    (p : ∀ n, Xn n ⟶ X) →
    (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n))) →
    (∀ n, IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f) →
    [∀ n, IsClosedImmersion (p n)] →
    (i : ∀ n, Xn n ⟶ Xn (n + 1)) →
    (∀ n, i n ≫ p (n + 1) = p n) →
    (∀ n, i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n)) →
    (ℱ : ∀ n, (Xn n).Modules) →
    [∀ n, (ℱ n).IsFinitePresentation] →
    (∀ n, Scheme.Modules.flatOver (ℱ n) (q n)) →
    [∀ n, Scheme.Modules.HasProperSupportOver (q n) (ℱ n)] →
    (φ : ∀ n,
      (Scheme.Modules.pullback (i n)).obj (ℱ (n + 1)) ⟶ ℱ n) →
    [∀ n, IsIso (φ n)] →
    AlgebraicGeometry.Scheme.Modules.ProperFlatFormalSystem)
