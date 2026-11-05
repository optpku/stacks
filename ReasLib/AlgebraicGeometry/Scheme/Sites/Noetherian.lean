/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Over

/-- Locally Noetherian schemes over a base scheme `S`. -/
def locallyNoetherian (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X ↦ IsLocallyNoetherian X.left

/-- Membership in `locallyNoetherian S` is local Noetherianity of the
underlying scheme. -/
theorem locallyNoetherian_iff {S : Scheme.{u}} (X : Over S) :
    locallyNoetherian S X ↔ IsLocallyNoetherian X.left := Iff.rfl

end AlgebraicGeometry.Scheme.Over

namespace AlgebraicGeometry.StandardTopology

/-- The standard Grothendieck topology restricted to locally Noetherian
schemes over `S`. -/
abbrev locallyNoetherianTopology (τ : StandardTopology) (S : Scheme.{u}) :
    GrothendieckTopology (Scheme.Over.locallyNoetherian S).FullSubcategory :=
  (Scheme.Over.locallyNoetherian S).ι.restrictedTopology (τ.overTopology S)

end AlgebraicGeometry.StandardTopology

namespace AlgebraicGeometry

/-- The inclusion of locally Noetherian schemes over `Spec (ZMod p)`, equipped
with the restricted fppf topology, into the big fppf site is continuous. -/
instance locallyNoetherianInclusion_fppf_isContinuous
    (p : ℕ) [Fact p.Prime] :
    let base := Spec (CommRingCat.of (ZMod p))
    let noetherian := Scheme.Over.locallyNoetherian base
    let topology := Scheme.fppfTopology.over base
    noetherian.ι.IsContinuous (StandardTopology.locallyNoetherianTopology .fppf base)
      topology := sorry

/-- Compatibility with the explicit predicate used by older site statements. -/
instance (priority := 100) locallyNoetherianInclusion_fppf_isContinuous_legacy
    (p : ℕ) [Fact p.Prime] :
    let base := Spec (CommRingCat.of (ZMod p))
    let noetherian : ObjectProperty (Over base) :=
      fun object => IsLocallyNoetherian object.left
    let topology := Scheme.fppfTopology.over base
    noetherian.ι.IsContinuous (noetherian.ι.restrictedTopology topology) topology :=
  locallyNoetherianInclusion_fppf_isContinuous p

/-- The left adjoint on set-valued sheaves associated to the inclusion of
locally Noetherian schemes over `Spec (ZMod p)` into the big fppf site does not
preserve finite limits. -/
theorem not_preservesFiniteLimits_locallyNoetherianInclusion_fppf
    (p : ℕ) [Fact p.Prime] :
    let base := Spec (CommRingCat.of (ZMod p))
    let noetherian := Scheme.Over.locallyNoetherian base
    let topology := Scheme.fppfTopology.over base
    ¬ PreservesFiniteLimits
      (noetherian.ι.sheafPullback (Type 1)
        (StandardTopology.locallyNoetherianTopology .fppf base) topology) := sorry

end AlgebraicGeometry

open AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- The category of locally Noetherian schemes over a nonempty locally
Noetherian base does not have all pullbacks. -/
theorem not_hasPullbacks_locallyNoetherian
    (S : Scheme.{u}) [IsLocallyNoetherian S] [Nonempty S] :
    ¬ HasPullbacks (Scheme.Over.locallyNoetherian S).FullSubcategory := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.StandardTopology

open Scheme.Over

/-- Restriction of a set-valued presheaf on `Over S` along the inclusion of
locally Noetherian schemes over `S`. -/
def restrictPresheaf (S : Scheme.{u}) :
    ((Over S)ᵒᵖ ⥤ Type (u + 1)) ⥤
      ((locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)) :=
  (Functor.whiskeringLeft _ _ _).obj (locallyNoetherian S).ι.op

/-- The object map of `restrictPresheaf` is precomposition with the opposite of
the inclusion of locally Noetherian schemes over `S`. -/
theorem restrictPresheaf_obj (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    (restrictPresheaf S).obj F = (locallyNoetherian S).ι.op ⋙ F := sorry

end AlgebraicGeometry.StandardTopology
