module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The inclusion of locally Noetherian schemes over `Spec (ZMod p)`, equipped
with the restricted fppf topology, into the big fppf site is continuous. -/
instance locallyNoetherianInclusion_fppf_isContinuous
    (p : ℕ) [Fact p.Prime] :
    let base := Spec (CommRingCat.of (ZMod p))
    let noetherian : ObjectProperty (Over base) :=
      fun object => IsLocallyNoetherian object.left
    let topology := Scheme.fppfTopology.over base
    noetherian.ι.IsContinuous (noetherian.ι.restrictedTopology topology) topology := sorry

/-- The left adjoint on set-valued sheaves associated to the inclusion of
locally Noetherian schemes over `Spec (ZMod p)` into the big fppf site does not
preserve finite limits. -/
theorem not_preservesFiniteLimits_locallyNoetherianInclusion_fppf
    (p : ℕ) [Fact p.Prime] :
    let base := Spec (CommRingCat.of (ZMod p))
    let noetherian : ObjectProperty (Over base) :=
      fun object => IsLocallyNoetherian object.left
    let topology := Scheme.fppfTopology.over base
    ¬ PreservesFiniteLimits
      (noetherian.ι.sheafPullback (Type 1)
        (noetherian.ι.restrictedTopology topology) topology) := sorry

end AlgebraicGeometry
