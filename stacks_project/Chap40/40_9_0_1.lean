/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Presentation

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.GroupoidScheme

universe u

section

variable {S : Scheme.{u}} {U' : Over S} (G : GroupoidScheme S) (g : U' ⟶ G.U)

/- 40.9.0.1: `pullbackArrowIso G g` identifies the restricted arrow scheme with the
iterated pullback of `pullback.fst G.s.left g.left` and `pullback.snd g.left G.t.left`
over `G.R.left`. -/
@[stacks 04MN] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackArrowIso G g :
    (G.toPreRelation.pullback g).left ≅
      Limits.pullback (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t))

/- Under the presentation isomorphism, the upper route to `G.R` is the canonical
restricted-arrow projection. -/
#check
  (AlgebraicGeometry.GroupoidScheme.pullbackArrowIso_hom_upper_fst G g :
    (AlgebraicGeometry.GroupoidScheme.pullbackArrowIso G g).hom ≫
          Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.fst G.s g =
      AlgebraicGeometry.GroupoidScheme.pullbackArrow G g)

/- Under the presentation isomorphism, the upper projection to `U'` is the restricted
source map. -/
#check
  (AlgebraicGeometry.GroupoidScheme.pullbackArrowIso_hom_upper_snd G g :
    (AlgebraicGeometry.GroupoidScheme.pullbackArrowIso G g).hom ≫
          Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.snd G.s g =
      (G.toPreRelation.pullback g).s)

/- Under the presentation isomorphism, the lower projection to `U'` is the restricted
target map. -/
#check
  (AlgebraicGeometry.GroupoidScheme.pullbackArrowIso_hom_lower_fst G g :
    (AlgebraicGeometry.GroupoidScheme.pullbackArrowIso G g).hom ≫
          Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.fst g G.t =
      (G.toPreRelation.pullback g).t)

/- Under the presentation isomorphism, the lower route to `G.R` is the canonical
restricted-arrow projection. -/
#check
  (AlgebraicGeometry.GroupoidScheme.pullbackArrowIso_hom_lower_snd G g :
    (AlgebraicGeometry.GroupoidScheme.pullbackArrowIso G g).hom ≫
          Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.snd g G.t =
      AlgebraicGeometry.GroupoidScheme.pullbackArrow G g)

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
