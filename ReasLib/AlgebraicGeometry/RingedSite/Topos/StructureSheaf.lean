module

public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.AlgebraicGeometry.RingedSite.Topos
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying structure sheaves of ringed sites

This leaf owns the coefficient-forgetful view of a ringed site's structure sheaf.  It sits below
arbitrary ringed-topos morphisms and ringed-site `2`-morphisms so both APIs can reuse the same
object without a dependency between those layers.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

/-- The underlying type-valued sheaf of the structure sheaf of a ringed site. -/
@[stacks 01D3 "underlying structure sheaf"]
abbrev underlyingStructureSheaf (X : RingedSite.{uX, vX, w})
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})] :
    Sheaf X.siteTopology (Type w) :=
  (sheafCompose X.siteTopology (forget RingCat.{w})).obj X.structureSheaf

/-- Forgetting rings after direct image of a structure sheaf agrees with direct image of its
underlying type-valued sheaf. -/
theorem structureSheafPushforward_eq
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
    (f : X.Hom Y) :
    (sheafCompose Y.siteTopology (forget RingCat.{w})).obj
        ((f.base.sheafPushforwardContinuous RingCat.{w}
          Y.siteTopology X.siteTopology).obj X.structureSheaf) =
      (f.base.sheafPushforwardContinuous (Type w)
        Y.siteTopology X.siteTopology).obj (underlyingStructureSheaf X) := sorry

/-- The pushforward-form map on underlying structure sheaves associated to a ringed-site
morphism. -/
abbrev underlyingDirectImageMap
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
    (f : X.Hom Y) :
    underlyingStructureSheaf Y ⟶
      (f.base.sheafPushforwardContinuous (Type w)
        Y.siteTopology X.siteTopology).obj (underlyingStructureSheaf X) :=
  (sheafCompose Y.siteTopology (forget RingCat.{w})).map f.structureSheafMap ≫
    eqToHom (structureSheafPushforward_eq f)

/-- The inverse-image-form map on underlying structure sheaves associated to a ringed-site
morphism whose sheaf pullback is left exact. -/
noncomputable abbrev underlyingInverseImageMap
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vX, w}]
    (f : X.Hom Y)
    [PreservesFiniteLimits
      (f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology)] :
    (f.toMorphismOfTopoi).inverseImage.obj (underlyingStructureSheaf Y) ⟶
      underlyingStructureSheaf X :=
  ((f.base.sheafAdjunctionContinuous (Type w)
      Y.siteTopology X.siteTopology).homEquiv _ _).symm f.underlyingDirectImageMap

-- The sheaf itself is a direct coefficient-forgetful view; the maps only add equality and
-- adjunction coherence to the explicit structure-sheaf map.

end RingedSite.Hom
