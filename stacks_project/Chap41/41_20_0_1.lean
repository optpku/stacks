/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale

open CategoryTheory

universe u

/-
41.20.0.1: For every morphism `f : X ⟶ S`, base change sends a scheme étale over `S`
to its canonical singleton descent datum relative to `X/S`, whose component is étale over `X`.
-/
@[stacks 0BTI] #check
  (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      S.Etale ⥤ AlgebraicGeometry.Scheme.DescentData.Etale f)
