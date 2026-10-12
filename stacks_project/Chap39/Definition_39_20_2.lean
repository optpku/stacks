/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 39.20.2 (1): a pre-relation has a representable quotient when its
quotient sheaf is representable. -/
@[stacks 03BD] #check
  (AlgebraicGeometry.Scheme.PreRelation.HasRepresentableQuotient :
    ∀ {S : Scheme.{u}}, StandardTopology →
      ∀ {U : Over S}, Scheme.PreRelation U → Prop)

/- Definition 39.20.2 (2): a groupoid scheme has a representable quotient when
the quotient sheaf of its underlying pre-relation `(t, s)` is representable. -/
@[stacks 03BD] #check
  (AlgebraicGeometry.GroupoidScheme.HasRepresentableQuotient :
    ∀ {S : Scheme.{u}}, StandardTopology → GroupoidScheme S → Prop)
