/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Flat
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/- Lemma 29.25.16: if `f : X ⟶ Y` is flat and `g : V ⟶ Y` is quasi-compact, then the
scheme-theoretic image of `pullback.snd g f` is the inverse image of the
scheme-theoretic image of `g`. -/
@[stacks 081I] #check (AlgebraicGeometry.Scheme.Hom.image_pullback_snd_of_flat :
  ∀ {X Y V : Scheme.{u}} (f : X ⟶ Y) [Flat f] (g : V ⟶ Y) [QuasiCompact g],
    Scheme.Hom.image (pullback.snd g f) = (g.ker.comap f).subscheme)
