/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange
import StacksCheckRecall

/-!
# Lemma 18.41.4

Compatibility facade for module base change from direct-image presentations of the two vertical
pullbacks. A `PullbackPresentation` abstracts the module-level consequence supplied by the
continuous/cocontinuous site presentation and inverse-image structure-sheaf condition; it is not
an equivalent encoding of that geometric input. The equality of composite ringed-site morphisms
retains the structure-ring compatibility omitted by a bare square of underlying functors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w z

namespace RingedSite.Hom.PullbackPresentation

variable {X' : RingedSite.{u₀, v₀, w}} {X : RingedSite.{u₁, v₁, w}}
variable {Y' : RingedSite.{u₂, v₂, w}} {Y : RingedSite.{u₃, v₃, w}}
variable (g' : Hom X' X) (f' : Hom X' Y') (f : Hom X Y) (g : Hom Y' Y)
variable [(g'.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]
variable (pg' : PullbackPresentation g') (pg : PullbackPresentation g)
variable (h : Hom.comp pg'.pushforwardHom f' = Hom.comp f pg.pushforwardHom)

/- Lemma 18.41.4 (0FN4) (1): module direct image commutes with the two presented vertical
inverse images. -/
@[stacks 0FN4 "(1)"]
#check ((pg'.baseChangeIso pg h).symm :
  g'.modulePullback.{z} ⋙ f'.modulePushforward.{z} ≅
    f.modulePushforward.{z} ⋙ g.modulePullback.{z})

/- The canonical comparison map underlying clause (1). -/
#check (pg'.comparison pg h :
  f.modulePushforward.{z} ⋙ g.modulePullback.{z} ⟶
    g'.modulePullback.{z} ⋙ f'.modulePushforward.{z})

section LowerShriek

variable [(f'.modulePushforward.{z}).IsRightAdjoint]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(g'.modulePullback.{z}).IsRightAdjoint]
variable [(g.modulePullback.{z}).IsRightAdjoint]

/- Lemma 18.41.4 (0FN4) (2): taking the mate gives lower-shriek/inverse-image base change. -/
@[stacks 0FN4 "(2)"]
#check (pg'.lowerShriekIso pg h :
  f'.modulePullback.{z} ⋙ g'.moduleLowerShriek ≅
    g.moduleLowerShriek ⋙ f.modulePullback.{z})

end LowerShriek

end RingedSite.Hom.PullbackPresentation
