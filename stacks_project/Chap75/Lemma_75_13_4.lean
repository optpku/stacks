module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Derived.RelativeTorDimension

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open RingedSite.Hom RingedSite.Hom.ModuleDerived

universe u

/- Lemma 75.13.4 (1): relative Tor-amplitude in a fixed interval is equivalent
before and after canonical small étale inverse image. -/
@[stacks 0DK7] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.hasTorAmplitudeInOver_iff :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) (a b : ℤ),
      HasTorAmplitudeInOver (zariskiCommRingedHom f) E a b ↔
        HasTorAmplitudeInOver (Scheme.Etale.Small.commRingedHom f)
          ((commSmallEtaleToZariskiDerived X).obj E) a b)

/- Lemma 75.13.4 (2): covering-local finite relative Tor dimension is equivalent
before and after canonical small étale inverse image. -/
@[stacks 0DK7] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.locallyHasFiniteTorDimensionOver_iff :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)),
      LocallyHasFiniteTorDimensionOver (zariskiCommRingedHom f) E ↔
        LocallyHasFiniteTorDimensionOver (Scheme.Etale.Small.commRingedHom f)
          ((commSmallEtaleToZariskiDerived X).obj E))
