/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Composition
import StacksCheckRecall

/-!
# Lemma 18.13.3

Direct and inverse images of module sheaves are pseudofunctorial under composition of morphisms
of ringed sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY uZ vZ w z

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}} (f : X.Hom Y) (g : Y.Hom Z)

/- Lemma 18.13.3 (1) (03D8): direct image along a composite is canonically the composite of
the direct-image functors. -/
@[stacks 03D8 "(1)"]
#check (RingedSite.Hom.modulePushforwardCompIso.{z} f g :
  f.modulePushforward.{z} ⋙ g.modulePushforward.{z} ≅
    (f.comp g).modulePushforward.{z})

variable [f.modulePushforward.{z}.IsRightAdjoint]
  [g.modulePushforward.{z}.IsRightAdjoint]

/- Lemma 18.13.3 (2) (03D8): inverse image along a composite is canonically the composite of
the inverse-image functors in contravariant order. -/
@[stacks 03D8 "(2)"]
#check (RingedSite.Hom.modulePullbackCompIso.{z} f g :
  compositePullback.{z} f g ≅ g.modulePullback.{z} ⋙ f.modulePullback.{z})

end RingedSite.Hom
