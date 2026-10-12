/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.StructureSheaf

/-!
# Forgetful comparison for ring-sheaf direct images

This leaf gives the ring-sheaf specialization of continuous direct image commuting with the
forgetful functor to type-valued sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ v₁ u₂ v₂ w

namespace Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
variable [J₁.HasSheafCompose (forget RingCat.{w})]
variable [J₂.HasSheafCompose (forget RingCat.{w})]

/-- Forgetting rings after continuous direct image agrees with direct image of the underlying
set-valued structure sheaf. -/
theorem pushforwardUnderlying_eq
    (u : C₁ ⥤ C₂) [u.IsContinuous J₁ J₂]
    (𝒪₂ : Sheaf J₂ RingCat.{w}) :
    (sheafCompose J₁ (forget RingCat.{w})).obj
        ((u.sheafPushforwardContinuous RingCat.{w} J₁ J₂).obj 𝒪₂) =
      (u.sheafPushforwardContinuous (Type w) J₁ J₂).obj
        (RingedSite.Hom.underlyingStructureSheaf (RingedSite.ofRingSheaf J₂ 𝒪₂)) := sorry

/-- An isomorphism of ring sheaves induces the corresponding isomorphism after continuous direct
image and forgetting ring structure. -/
noncomputable def pushforwardUnderlyingIso
    (u : C₁ ⥤ C₂) [u.IsContinuous J₁ J₂]
    {𝒪₂ : Sheaf J₂ RingCat.{w}} {𝒪₁ : Sheaf J₁ RingCat.{w}}
    (e : (u.sheafPushforwardContinuous RingCat.{w} J₁ J₂).obj 𝒪₂ ≅ 𝒪₁) :
    (u.sheafPushforwardContinuous (Type w) J₁ J₂).obj
        (RingedSite.Hom.underlyingStructureSheaf (RingedSite.ofRingSheaf J₂ 𝒪₂)) ≅
      RingedSite.Hom.underlyingStructureSheaf (RingedSite.ofRingSheaf J₁ 𝒪₁) :=
  (eqToIso (pushforwardUnderlying_eq (J₁ := J₁) (J₂ := J₂) u 𝒪₂)).symm ≪≫
    (sheafCompose J₁ (forget RingCat.{w})).mapIso e

end Functor

-- The isomorphism is assembled from the canonical direct-image comparison and the supplied
-- ring-sheaf isomorphism; deferred proof debt is confined to the comparison theorem.
