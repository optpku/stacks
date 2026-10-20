/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.AmbientSquare
import StacksCheckRecall

/-!
# Lemma 18.20.1

Compatibility facade for the reusable square of localized ringed topoi.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vX, w}] [UnivLE.{max uY vY vX, w}]
  (f : X.Hom Y) (V : Y)

/- Lemma 18.20.1 (04J0): localization at `f.base.obj V` and `V` gives the canonical
commutative square of ringed topoi. -/
@[stacks 04J0]
#check (Localization.AmbientSquare.square f (𝟙 (f.base.obj V)) :
  ToposHom.LaxCommSquare
    (X.localization (f.base.obj V)) X (Y.localization V) Y)

/- Lemma 18.20.1 (04J0): the square commutes by an invertible `2`-morphism, available
directly to typeclass search. -/
@[stacks 04J0 "(invertible square)"]
#check (inferInstance :
  (Localization.AmbientSquare.square f (𝟙 (f.base.obj V))).IsInvertible)

end RingedSite.Hom
