/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.FieldExtension

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.15.1: Let `k` be a field and `X` a scheme over `k`. If the base change of `X` to
some field extension `K/k` admits an ample invertible module, then so does `X`. -/
@[stacks 0BDC] #check
  (AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule.of_baseChangeToFieldExtension :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)),
      Scheme.Modules.HasAmpleInvertibleModule (FieldExtension.baseChange k K f) →
        Scheme.Modules.HasAmpleInvertibleModule X)
