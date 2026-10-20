/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.ReducedImageClosure.Groupoid
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Field
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Properties
public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# Locally closed ranges of morphisms of groupoid schemes

This module records a closedness criterion for the arrow-image of a morphism of groupoid schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/-- For an identity-on-objects morphism of groupoid schemes over a field spectrum, a locally
closed arrow-image is closed. -/
theorem isClosed_range_of_isLocallyClosed {S : Scheme.{u}} {k : Type u} [Field k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    (h_locallyClosed : IsLocallyClosed (Set.range f.arrow.left)) :
    IsClosed (Set.range f.arrow.left) := sorry

end AlgebraicGeometry.GroupoidScheme.Hom
