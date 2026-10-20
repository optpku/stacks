/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.AmbientSquare
import StacksCheckRecall

/-!
# Lemma 18.20.2

Both diagrams are exposed by reusable localization-square APIs.  Their underlying slice-site
comparisons remain available as fine-grained Beck--Chevalley infrastructure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

section Ambient

variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vX, w}] [UnivLE.{max uY vY vX, w}]
variable (f : X.Hom Y) {V : Y} {U : X} (c : U ⟶ f.base.obj V)

/- Lemma 18.20.2 (1) (04J1): the localized morphism from the localization at `U` to the
localization at `V`. -/
@[stacks 04J1 "(1), localized morphism"]
#check (f.localizationAt V c : ToposHom (X.localization U) (Y.localization V))

/- Lemma 18.20.2 (1) (04J1): the canonical forward `2`-morphism between the two paths from
the localization at `U` to the ambient ringed topos of `Y`. -/
@[stacks 04J1 "(1), ambient comparison"]
#check (Localization.AmbientSquare.comparison f c :
  ToposHom.TwoMorphism
    (ToposHom.comp (Localization.toAmbient X U) f.toToposHom)
    (ToposHom.comp (f.localizationAt V c) (Localization.toAmbient Y V)))

/- Lemma 18.20.2 (1) (04J1): the comparison in the ambient localization square is
invertible on its underlying direct-image natural transformation. -/
@[stacks 04J1 "(1), invertible comparison"]
#check (inferInstance :
  IsIso (Localization.AmbientSquare.comparison f c).hom)

/- Lemma 18.20.2 (1) (04J1): the reusable square contains all four morphisms of ringed
topoi and their forward `2`-cell. -/
@[stacks 04J1 "(1), ambient square"]
#check (Localization.AmbientSquare.square f c :
  ToposHom.LaxCommSquare (X.localization U) X (Y.localization V) Y)

/- Lemma 18.20.2 (1) (04J1): invertibility of the ambient square is available to typeclass
search without choosing inverse `2`-cell data. -/
@[stacks 04J1 "(1), invertible square"]
#check (inferInstance :
  (Localization.AmbientSquare.square f c).IsInvertible)

end Ambient

section Functoriality

variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vY vX, w}]
variable (f : X.Hom Y)
variable {V V' : Y} {U U' : X}
variable (c : U ⟶ f.base.obj V) (b : V' ⟶ V) (a : U' ⟶ U)
variable (c' : U' ⟶ f.base.obj V') (hcomm : c' ≫ f.base.map b = a ≫ c)

/- Lemma 18.20.2 (2) (04J1): the canonical forward `2`-morphism between the two composites
of localized morphisms and relocalizations. -/
@[stacks 04J1 "(2), comparison"]
#check (Localization.RelocalizationSquare.comparison f c b a c' hcomm :
  ToposHom.TwoMorphism
    (ToposHom.comp (Localization.relocalization X a) (f.localizationAt V c))
    (ToposHom.comp (f.localizationAt V' c') (Localization.relocalization Y b)))

/- Lemma 18.20.2 (2) (04J1): the reusable square contains all four morphisms of ringed
topoi and their forward `2`-cell. -/
@[stacks 04J1 "(2), relocalization square"]
#check (Localization.RelocalizationSquare.square f c b a c' hcomm :
  ToposHom.LaxCommSquare
    (X.localization U') (X.localization U)
    (Y.localization V') (Y.localization V))

/- Lemma 18.20.2 (2) (04J1): invertibility of the relocalization square is available to
typeclass search without choosing inverse `2`-cell data. -/
@[stacks 04J1 "(2), invertible square"]
#check (inferInstance :
  (Localization.RelocalizationSquare.square f c b a c' hcomm).IsInvertible)

/- The functor-level inverse-image square is the fine-grained site-theoretic core of the
ringed-topos comparison above. -/
#check
  (X.siteTopology.overMapPullbackSquare (Type w)
    a c' c (f.base.map b) hcomm.symm :
      X.siteTopology.overMapPullback (Type w) c ⋙
          X.siteTopology.overMapPullback (Type w) a ≅
        X.siteTopology.overMapPullback (Type w) (f.base.map b) ⋙
          X.siteTopology.overMapPullback (Type w) c')

end Functoriality

end RingedSite.Hom
