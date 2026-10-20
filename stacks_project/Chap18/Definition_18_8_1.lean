/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
import StacksCheckRecall

@[expose] public section

/-!
# Definition 18.8.1

Compatibility facade for the presentation-independent structure-sheaf `2`-morphism API.
-/

open CategoryTheory

universe uX vX uY vY uZ vZ w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable {f g : ToposHom X Y}

/- Definition 18.8.1: a `2`-morphism between arbitrary ringed-topos morphisms is a
direct-image transformation whose canonical lift to ring-valued sheaves is compatible with the
two structure-sheaf maps. -/
@[stacks 04IC]
#check (TwoMorphism f g)

variable {k : ToposHom X Y}
variable (η : TwoMorphism f g) (θ : TwoMorphism g k)

/- Vertical composition is supplied by the same reusable owner API. -/
#check (η.comp θ : TwoMorphism f k)

section HorizontalComposition

variable {Z : RingedSite.{uZ, vZ, w}}
variable [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable {p q : ToposHom Y Z} (μ : TwoMorphism p q)

/- Horizontal composition works across a third site with independent site universes. -/
#check (η.hcomp μ :
  TwoMorphism (ToposHom.comp f p) (ToposHom.comp g q))

end HorizontalComposition

end RingedSite.ToposHom
