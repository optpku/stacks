/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.43.3 (1): an H-projective morphism is H-quasi-projective. -/
@[stacks 01W9] #check
  (AlgebraicGeometry.HProjective.toHQuasiProjective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.HProjective f → AlgebraicGeometry.HQuasiProjective f)

/- Lemma 29.43.3 (2): an H-projective morphism is projective. -/
@[stacks 01W9] #check
  (AlgebraicGeometry.HProjective.toProjective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.HProjective f → AlgebraicGeometry.Projective f)
