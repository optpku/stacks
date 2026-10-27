/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.AffineFppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf

/-!
# Actual coefficient sheaves for the same-universe forward comparison

The affine coefficient sheaf is the restriction of the lifted global-functions
sheaf. Its underlying presheaf agrees with the chaotic affine coefficients by
the identity ring maps. No commutative-ring sheafification or identity Kan
extension is selected here.
-/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open RingedSite RingedSite.Hom
noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- Lift actual global-function rings and restriction maps to the common universe. -/
abbrev liftedFppfStructureSheaf :
    Sheaf (ringedSite X).siteTopology RingCat.{u + 1} :=
  (sheafCompose (ringedSite X).siteTopology
    (Scheme.Site.ringUniverseLift.{u, u + 1})).obj (ringedSite X).structureSheaf

/-- The fppf ringed site with those same explicitly lifted coefficients. -/
abbrev liftedFppfRingedSite : RingedSite.{u + 1, u, u + 1} :=
  ofRingSheaf (ringedSite X).siteTopology (liftedFppfStructureSheaf X)

/-- Restriction to the affine basis preserves sheaves for the inherited topology. -/
instance affineInclusion_isContinuous_fppf :
    (affineInclusion X).IsContinuous (affineSiteFppfTopology X)
      (ringedSite X).siteTopology := sorry

/-- Literal restriction of the global-functions sheaf to affine objects. -/
abbrev affineFppfRestrictedStructureSheaf :
    Sheaf (affineSiteFppfTopology X) RingCat.{u + 1} :=
  ((affineInclusion X).sheafPushforwardContinuous RingCat.{u + 1}
    (affineSiteFppfTopology X) (ringedSite X).siteTopology).obj
      (liftedFppfStructureSheaf X)

/-- The affine fppf module site, with actual restricted coefficients. -/
abbrev affineFppfRingedSite : RingedSite.{u + 1, u, u + 1} :=
  ofRingSheaf (affineSiteFppfTopology X) (affineFppfRestrictedStructureSheaf X)

/-- The chaotic and fppf affine coefficient presheaves have the same rings
and restriction maps; both directions are identity ring maps. -/
def affineCoefficientPresheafIso :
    (ofCommRingSheaf ⊥ (affineStructureSheaf X)).structureSheaf.obj ≅
      (affineFppfRestrictedStructureSheaf X).obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    ext x
    rfl)

end AlgebraicGeometry.GroupoidsOver
