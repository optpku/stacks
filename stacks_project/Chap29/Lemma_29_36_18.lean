/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Over

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 29.36.18: Let `f : X ⟶ Y` be a morphism of schemes over `S`. If `X` and `Y`
are étale over `S`, then `f` is étale. -/
@[stacks 02GW] #check (AlgebraicGeometry.etale_of_etale_over :
  ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
    Etale X.hom → Etale Y.hom → Etale f.left)
