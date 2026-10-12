/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Ambient
import StacksCheckRecall

/-!
# Lemma 18.19.5

Compatibility facade for the reusable ambient-localization triangle API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace RingedSite.Localization

variable (X : RingedSite.{u, v, w}) [UnivLE.{max u v, w}]
variable {U V : X} (f : V ⟶ U)

/- Lemma 18.19.5 (04IY): localization at `U` gives a canonical morphism from the localized
ringed topos to the ambient ringed topos. -/
@[stacks 04IY "ambient localization"]
#check (toAmbient X U : ToposHom (X.localization U) X)

variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]

/- Lemma 18.19.5 (04IY): for `f : V ⟶ U`, relocalization from `V` to `U` followed by the
ambient-localization morphism is canonically `2`-isomorphic to localization at `V`. -/
@[stacks 04IY "commutative triangle"]
#check (relocalizationTriangle X f :
  ToposHom.TwoIso (ToposHom.comp (relocalization X f) (toAmbient X U)) (toAmbient X V))

end RingedSite.Localization
