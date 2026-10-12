/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.QuasiProjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 33.15.3: quasi-projectivity over a field descends along an arbitrary extension of the
ground field. -/
@[stacks 0BDE] #check
  (AlgebraicGeometry.QuasiProjective.of_baseChangeToFieldExtension :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)),
      QuasiProjective (FieldExtension.toBase k K f) → QuasiProjective f)
