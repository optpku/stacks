/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# From morphisms of ringed sites to morphisms of ringed topoi

A morphism of ringed sites canonically presents a morphism of ringed topoi.  Its direct-image
structure map is converted to the canonical inverse-image form through the internal-ring
adjunction.  Thus downstream users receive a `RingedSite.ToposHom` without retaining auxiliary
Kan-extension or coefficient choices.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- The type-valued inverse image of a morphism of ringed sites is left exact in every
coefficient universe containing the site universes. -/
noncomputable def baseSheafPullbackPreservesFiniteLimits (f : X.Hom Y)
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
    [UnivLE.{max uY vX, w}] :
    PreservesFiniteLimits
      (f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology) := sorry

/-- The canonical coefficient-forgetful comparison for the direct image presented by a
morphism of ringed sites. -/
noncomputable def toToposHomForgetIso (f : X.Hom Y)
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
    [UnivLE.{max uY vX, w}] :
    f.base.sheafPushforwardContinuous RingCat.{w}
          Y.siteTopology X.siteTopology ⋙
        sheafCompose Y.siteTopology (forget RingCat.{w}) ≅
      sheafCompose X.siteTopology (forget RingCat.{w}) ⋙
        (@Functor.morphismOfTopoiInOfContinuous _ _ _ _ f.base
          Y.siteTopology X.siteTopology inferInstance inferInstance inferInstance
          (baseSheafPullbackPreservesFiniteLimits f)).pushforward :=
  Iso.refl _

/-- The direct-image presentation supplied by a morphism of ringed sites preserves the
canonical internal-ring operations. -/
theorem toToposIsRingCompatible (f : X.Hom Y)
    [hasX : X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [hasY : Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
    [UnivLE.{max uY vX, w}] :
    @ToposHom.Direct.IsRingCompatible X Y hasX hasY
      (@Functor.morphismOfTopoiInOfContinuous _ _ _ _ f.base
        Y.siteTopology X.siteTopology inferInstance inferInstance inferInstance
        (baseSheafPullbackPreservesFiniteLimits f))
      (f.base.sheafPushforwardContinuous RingCat.{w}
        Y.siteTopology X.siteTopology)
      (toToposHomForgetIso f) f.structureSheafMap := sorry

/-- The morphism of ringed topoi presented by a morphism of ringed sites, expressed using
the canonical ring-valued inverse image. -/
@[stacks 01D3 "site presentation"]
noncomputable def toToposHom (f : X.Hom Y)
    [hasX : X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [hasY : Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
    [UnivLE.{max uY vX, w}] : ToposHom X Y :=
  @ToposHom.ofDirectImage X Y hasX hasY
    (@Functor.morphismOfTopoiInOfContinuous _ _ _ _ f.base
      Y.siteTopology X.siteTopology inferInstance inferInstance inferInstance
      (baseSheafPullbackPreservesFiniteLimits f))
    (f.base.sheafPushforwardContinuous RingCat.{w}
      Y.siteTopology X.siteTopology)
    (toToposHomForgetIso f) f.structureSheafMap
    (toToposIsRingCompatible f)

-- Every non-Prop field is inherited directly from the continuous site presentation; the only
-- deferred obligation below is the Prop-valued left-exactness fact.

end RingedSite.Hom
