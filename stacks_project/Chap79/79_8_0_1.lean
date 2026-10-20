/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.Presentation

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.GroupoidAlgebraicSpace

universe u

section

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U' : Over B}
  (G : GroupoidAlgebraicSpace B) (g : U' ⟶ G.U)

/- 79.8.0.1: `pullbackArrowIso G g` identifies the restricted arrow space with the
iterated pullback of `pullback.fst G.s g` and `pullback.snd g G.t` over `G.R`. -/
@[stacks 04RN] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso G g :
    (G.toPreRelation.pullback g).left ≅
      Limits.pullback (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t))

/- Under the presentation isomorphism, the upper route to `G.R` is the canonical
restricted-arrow projection. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso_hom_upper_fst G g :
    (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso G g).hom ≫
          Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.fst G.s g =
      AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrow G g)

/- Under the presentation isomorphism, the upper projection to `U'` is the restricted
source map. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso_hom_upper_snd G g :
    (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso G g).hom ≫
          Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.snd G.s g =
      (G.toPreRelation.pullback g).s)

/- Under the presentation isomorphism, the lower projection to `U'` is the restricted
target map. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso_hom_lower_fst G g :
    (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso G g).hom ≫
          Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.fst g G.t =
      (G.toPreRelation.pullback g).t)

/- Under the presentation isomorphism, the lower route to `G.R` is the canonical
restricted-arrow projection. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso_hom_lower_snd G g :
    (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso G g).hom ≫
          Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.snd g G.t =
      AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrow G g)

/- The upper-left square in the iterated pullback presentation is cartesian. -/
#check
  (CategoryTheory.IsPullback.of_hasPullback
      (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) :
    CategoryTheory.IsPullback
      (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t))
      (Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t))
      (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t))

/- The upper-right square in the iterated pullback presentation is cartesian. -/
#check
  (CategoryTheory.IsPullback.of_hasPullback G.s g :
    CategoryTheory.IsPullback (Limits.pullback.fst G.s g) (Limits.pullback.snd G.s g)
      G.s g)

/- The lower-left square in the iterated pullback presentation is cartesian. -/
#check
  (CategoryTheory.IsPullback.of_hasPullback g G.t :
    CategoryTheory.IsPullback (Limits.pullback.fst g G.t) (Limits.pullback.snd g G.t)
      g G.t)

end
