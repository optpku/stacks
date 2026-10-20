/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf.OpenImmersion
import StacksCheckRecall

/-!
# Finding opens in groupoid quotients

If the saturation morphism of a restriction of a groupoid scheme has open image and the
corestriction onto that image is an fppf sheaf surjection, then the induced map of fppf
quotient sheaves is a representable open immersion.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 80.7.1 -/
@[stacks 046M]
#check (AlgebraicGeometry.GroupoidScheme.pullbackQuotientMap_isOpenImmersion :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.U)
    (W : G.U.left.Opens)
    (hToImage : Limits.pullback g G.t ⟶ Over.mk (W.ι ≫ G.U.hom))
    (h_range : Set.range (((Limits.pullback.snd g G.t) ≫ G.s).left.base) =
      (W : Set G.U.left))
    (h_factor : hToImage.left ≫ W.ι = ((Limits.pullback.snd g G.t) ≫ G.s).left)
    (h_surj : Sheaf.IsLocallySurjective
      ((Scheme.fppfTopology.over S).uliftSheafifiedRepresentableMap.{u + 1} hToImage)),
    (MorphismProperty.over (@IsOpenImmersion)).relative uliftYoneda.{u + 1}
      ((G.toPreRelation.pullbackHom g).quotientSheafMap (Scheme.fppfTopology.over S)).hom)

end AlgebraicGeometry.GroupoidScheme
