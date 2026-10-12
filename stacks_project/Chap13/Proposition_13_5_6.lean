/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.MorphismProperty.Localization.Triangulated.Characterization
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

/- Domain-style sampling:
- primary domain: localization of pretriangulated and triangulated categories by a multiplicative
  system compatible with distinguished triangles;
- relevant upstream owner declarations in this domain:
  `MorphismProperty.commShift_Q`,
  `Triangulated.Localization.pretriangulated`,
  `Triangulated.Localization.isTriangulated_functor`,
  `Functor.IsLocalization.distTriang_iff`;
- source/core/bridge triage:
  `source-facing`: the Verdier-localized category carries distinguished triangles coming from the
    essential image of distinguished triangles upstairs;
  `core/canonical`: the owner API in `CategoryTheory.Localization.Triangulated`;
  `bridge/view`: `MorphismProperty.Localization.distTriang_iff`, specialized to the localization functor
    `W.Q`.

Primitive data is the localization functor `W.Q` together with the compatible-triangulation
hypothesis on `W`. The pretriangulated structure on `W.Localization`, exactness of `W.Q`, the
distinguished-triangle characterization, and the triangulated structure under `[IsTriangulated D]`
are all derived owner API, so this file should stay at direct canonical recall/use.
-/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

variable (W : MorphismProperty D) [W.HasLeftCalculusOfFractions]
  [W.HasRightCalculusOfFractions] [W.IsCompatibleWithTriangulation]

/- Companion recall: the localization functor `W.Q` commutes with the shift by `ℤ` via the
canonical instance `MorphismProperty.commShift_Q`. -/
#check @MorphismProperty.commShift_Q

/- Proposition 13.5.6: if `D` is pretriangulated and `W` is a multiplicative system compatible
with the triangulated structure, then, after fixing the canonical additive, shift, and
shift-comparison data on `W.Localization`, there is a unique pretriangulated structure making
`W.Q` exact. The companion recalls below record the more general construction, the distinguished
triangle characterization, and that `W.Localization` is triangulated whenever `D` is
triangulated. -/
@[stacks 05R6] #check
  (MorphismProperty.Localization.existsUniquePretriangulated W)

/- Canonical companion: construction of the target pretriangulated structure needs only the left
calculus of fractions. -/
#check @Triangulated.Localization.pretriangulated

/- Companion recall: with the canonical pretriangulated structure on `W.Localization`, the
localization functor `W.Q` is triangulated, i.e. exact. -/
#check @Triangulated.Localization.isTriangulated_functor

/- Companion recall: with the canonical pretriangulated structure on `W.Localization`, a triangle
is distinguished exactly when it lies in the essential image of distinguished triangles of `D`
under `W.Q`. -/
#check (MorphismProperty.Localization.distTriang_iff W)

/- Model-independent companion: the same characterization applies to any localization model and
does not expose essential surjectivity of the induced arrow functor as a caller-supplied instance. -/
#check @Functor.IsLocalization.distTriang_iff

/- Companion recall: exactness uniquely determines the target pretriangulated structure without
requiring a caller to install that structure as a temporary local instance. -/
#check @Triangulated.Localization.pretriangulated_eq_of_map_distinguished

/- Companion recall: the existence-and-uniqueness theorem is also available for any localization
model, under the weaker left-calculus hypothesis used by the canonical construction. -/
#check @Triangulated.Localization.existsUniquePretriangulated

variable [IsTriangulated D]

/- Companion recall: if the source category `D` is triangulated, then the localized category
`W.Localization` is triangulated. -/
#check @Triangulated.Localization.isTriangulated

end CategoryTheory
