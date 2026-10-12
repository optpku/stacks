/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.CohenMacaulay
import StacksCheckRecall

open CategoryTheory TopologicalSpace

universe u

/-
Lemma 29.29.4: A flat, locally finitely presented morphism with Cohen-Macaulay fibers admits a
pairwise-disjoint clopen decomposition of its source by relative dimension.
-/
@[stacks 02NM] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_relativeDimension_decomposition :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ S) [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.LocallyOfFinitePresentation f],
      (∀ s : S, AlgebraicGeometry.Scheme.CohenMacaulay (f.fiber s)) →
        ∃ U : ℕ → X.Opens,
          iSup U = ⊤ ∧
            Pairwise (fun d e ↦ Disjoint (U d : Set X) (U e : Set X)) ∧
            (∀ d, IsClopen (U d : Set X)) ∧
            ∀ d, AlgebraicGeometry.Scheme.Hom.RelativeDimension ((U d).ι ≫ f) d)
