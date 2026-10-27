/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Basic

/-!
# Vertical composition of ringed-site `2`-morphisms

This leaf provides identity and vertical composition for structure-sheaf-compatible direct-image
transformations.
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

/-- The identity direct-image transformation satisfies the structure-sheaf compatibility
condition. -/
theorem TwoMorphism.id_comm (f : Hom X Y) :
    (sheafCompose Y.siteTopology (forget RingCat.{w})).map f.structureSheafMap ≫
      structureSheafComponent
        (𝟙 (f.sheafPushforwardContinuous (A := Type w))) =
      (sheafCompose Y.siteTopology (forget RingCat.{w})).map f.structureSheafMap := sorry

/-- The identity `2`-morphism of a ringed-site morphism. -/
def TwoMorphism.id (f : Hom X Y) : TwoMorphism f f where
  hom := 𝟙 _
  comm := TwoMorphism.id_comm f

/-- The underlying natural transformation of the identity ringed-site `2`-morphism. -/
@[simp] theorem TwoMorphism.id_hom (f : Hom X Y) :
    (TwoMorphism.id f).hom =
      𝟙 (f.sheafPushforwardContinuous (A := Type w)) := sorry

/-- The composite direct-image transformation satisfies the structure-sheaf compatibility
condition. -/
theorem TwoMorphism.comp_comm
    {f g h : Hom X Y} (η : TwoMorphism f g) (θ : TwoMorphism g h) :
    (sheafCompose Y.siteTopology (forget RingCat.{w})).map f.structureSheafMap ≫
      structureSheafComponent (η.hom ≫ θ.hom) =
        (sheafCompose Y.siteTopology (forget RingCat.{w})).map h.structureSheafMap := sorry

/-- Vertical composition of ringed-site `2`-morphisms. -/
def TwoMorphism.comp
    {f g h : Hom X Y} (η : TwoMorphism f g) (θ : TwoMorphism g h) :
    TwoMorphism f h where
  hom := η.hom ≫ θ.hom
  comm := TwoMorphism.comp_comm η θ

/-- The underlying natural transformation of a vertical composite is the composite of the
underlying natural transformations. -/
@[simp] theorem TwoMorphism.comp_hom
    {f g h : Hom X Y} (η : TwoMorphism f g) (θ : TwoMorphism g h) :
    (η.comp θ).hom = η.hom ≫ θ.hom := sorry

end RingedSite.Hom
