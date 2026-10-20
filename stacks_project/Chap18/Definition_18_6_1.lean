/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 18.6.1

The textbook ringed-site object and its category are supplied by the reusable owner
`RingedSite` in `ReasLib.AlgebraicGeometry.RingedSite.Basic`.
-/

open CategoryTheory

universe u v w uX vX uY vY uZ vZ

/- Definition 18.6.1 (1): a site equipped with a sheaf of rings determines a ringed site. -/
@[stacks 03AD "(1)"]
#check (RingedSite.{u, v, w} : Type (max (max (u + 1) (v + 1)) (w + 1)))

variable (X : RingedSite.{uX, vX, w}) (Y : RingedSite.{uY, vY, w})

/- Definition 18.6.1 (2): morphisms of ringed sites are the bundled site morphisms with their
adjoint structure-sheaf maps. -/
@[stacks 03AD "(2)"]
#check (RingedSite.Hom X Y : Type (max uX vX uY vY w))

variable (Z : RingedSite.{uZ, vZ, w})
  (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)

/- Definition 18.6.1 (3): morphisms compose across independent site universes; the category
instance on each fixed universe level specializes this operation to `≫`. -/
@[stacks 03AD "(3)"]
#check (RingedSite.Hom.comp f g : RingedSite.Hom X Z)

#check (inferInstance : Category.{max u v w} (RingedSite.{u, v, w}))
