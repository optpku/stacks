/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
import StacksCheckRecall

@[expose] public section

/-!
# Definition 18.7.1

Source-facing checks for site-presented ringed topoi and their arbitrary morphisms.
-/

open CategoryTheory

universe uX vX uY vY uZ vZ w

namespace RingedSite

variable (X : RingedSite.{uX, vX, w}) (Y : RingedSite.{uY, vY, w})
  (Z : RingedSite.{uZ, vZ, w})
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]

/- Definition 18.7.1 (01D3) (1): a site-presented ringed topos consists of a site and its
structure sheaf. -/
@[stacks 01D3 "(1)"]
#check (RingedSite.{uX, vX, w} :
  Type (max (max (uX + 1) (vX + 1)) (w + 1)))

/- Definition 18.7.1 (01D3) (2): an arbitrary morphism of ringed topoi consists of an underlying
morphism of topoi and the canonical inverse-image map of structure sheaves
`f⁻¹𝒪_Y ⟶ 𝒪_X`.  Its direct-image form is derived by the ring-level adjunction. -/
@[stacks 01D3 "(2)"]
#check (ToposHom X Y)

variable (f : ToposHom X Y) (g : ToposHom Y Z)

/- Definition 18.7.1 (01D3) (3): arbitrary morphisms of ringed topoi compose. -/
@[stacks 01D3 "(3)"]
#check (ToposHom.comp f g : ToposHom X Z)

end RingedSite
