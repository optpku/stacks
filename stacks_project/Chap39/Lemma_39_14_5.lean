/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Colimits

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 39.14.5: for every scheme `S` and groupoid scheme `G` over `S`, the
category `G.QCoh` of equivariant quasi-coherent modules admits all small colimits. -/
@[stacks 077R] #check
  (AlgebraicGeometry.GroupoidScheme.QCoh.hasColimits :
    ∀ {S : Scheme.{u}}, (G : GroupoidScheme S) → HasColimits G.QCoh)
