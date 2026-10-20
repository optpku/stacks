/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.StructureSheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic structure-sheaf `2`-morphisms of ringed sites

This leaf owns the underlying direct-image transformation and its compatibility with the
structure-sheaf maps.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- The structure-sheaf component induced by a natural transformation between underlying
direct-image functors. -/
abbrev structureSheafComponent
    {f g : Hom X Y}
    (η :
      f.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology ⟶
        g.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology) :
    (sheafCompose Y.siteTopology (forget RingCat.{w})).obj
        ((f.base.sheafPushforwardContinuous RingCat.{w}
          Y.siteTopology X.siteTopology).obj X.structureSheaf) ⟶
      (sheafCompose Y.siteTopology (forget RingCat.{w})).obj
        ((g.base.sheafPushforwardContinuous RingCat.{w}
          Y.siteTopology X.siteTopology).obj X.structureSheaf) :=
  eqToHom (structureSheafPushforward_eq f) ≫
    η.app (underlyingStructureSheaf X) ≫
      eqToHom (structureSheafPushforward_eq g).symm

/-- Definition 18.8.1: a structure-sheaf-compatible `2`-morphism between morphisms of ringed
sites. -/
@[stacks 04IC]
structure TwoMorphism (f g : Hom X Y) where
  /-- The underlying natural transformation between direct-image functors on type-valued
  sheaves. -/
  hom :
    f.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology ⟶
      g.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology
  /-- Compatibility of the direct-image structure-sheaf maps. -/
  comm :
    (sheafCompose Y.siteTopology (forget RingCat.{w})).map f.structureSheafMap ≫
      structureSheafComponent hom =
        (sheafCompose Y.siteTopology (forget RingCat.{w})).map g.structureSheafMap

/-- The component of a ringed-site `2`-morphism on the forgotten structure sheaf. -/
abbrev TwoMorphism.structureSheafHom
    {f g : Hom X Y} (η : TwoMorphism f g) :
    (sheafCompose Y.siteTopology (forget RingCat.{w})).obj
        ((f.base.sheafPushforwardContinuous RingCat.{w}
          Y.siteTopology X.siteTopology).obj X.structureSheaf) ⟶
      (sheafCompose Y.siteTopology (forget RingCat.{w})).obj
        ((g.base.sheafPushforwardContinuous RingCat.{w}
          Y.siteTopology X.siteTopology).obj X.structureSheaf) :=
  structureSheafComponent η.hom

/-- A ringed-site `2`-morphism coerces to its underlying direct-image natural transformation. -/
instance {f g : Hom X Y} :
    CoeTC
      (TwoMorphism f g)
      (f.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology ⟶
        g.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology) where
  coe η := η.hom

/-- Ringed-site `2`-morphisms are determined by their underlying natural transformations. -/
@[ext] theorem TwoMorphism.ext
    {f g : Hom X Y} {η θ : TwoMorphism f g} (h : η.hom = θ.hom) : η = θ := sorry

end RingedSite.Hom
