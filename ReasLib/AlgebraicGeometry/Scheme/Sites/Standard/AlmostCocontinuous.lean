/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Almost cocontinuity of pullback along a closed immersion for the big syntomic sites. -/
instance pullback_isAlmostCocontinuous_syntomic
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    Functor.IsAlmostCocontinuous (Over.pullback f)
      (StandardTopology.syntomic.overTopology Y)
      (StandardTopology.syntomic.overTopology X) := sorry

/-- Almost cocontinuity of pullback along a closed immersion for the big smooth sites. -/
instance pullback_isAlmostCocontinuous_smooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    Functor.IsAlmostCocontinuous (Over.pullback f)
      (StandardTopology.smooth.overTopology Y)
      (StandardTopology.smooth.overTopology X) := sorry

/-- Almost cocontinuity of pullback along a closed immersion for the big étale sites. -/
instance pullback_isAlmostCocontinuous_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    Functor.IsAlmostCocontinuous (Over.pullback f)
      (StandardTopology.etale.overTopology Y)
      (StandardTopology.etale.overTopology X) := sorry

/-- For a closed immersion and a standard topology among syntomic, smooth, and étale,
pullback is almost cocontinuous between the corresponding big sites. -/
theorem pullback_isAlmostCocontinuous_of_closedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (τ : StandardTopology)
    (hτ : τ = .syntomic ∨ τ = .smooth ∨ τ = .etale) :
    Functor.IsAlmostCocontinuous (Over.pullback f)
      (τ.overTopology Y) (τ.overTopology X) := sorry

end AlgebraicGeometry.StandardTopology.Big
