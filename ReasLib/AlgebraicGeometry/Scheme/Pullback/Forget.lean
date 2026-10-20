module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting scheme pullbacks
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Remark 26.16.2: the forgetful functor from schemes to locally ringed
spaces preserves pullbacks. -/
@[stacks 01JN, instance]
instance Scheme.forgetToLocallyRingedSpace_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      Scheme.forgetToLocallyRingedSpace := sorry

/-- The underlying locally ringed-space maps of two scheme morphisms with a
common target admit a pullback. -/
@[stacks 01JN "underlying locally ringed-space pullback exists"]
instance Scheme.forgetToLocallyRingedSpace_hasPullback
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    HasPullback (Scheme.forgetToLocallyRingedSpace.map f)
      (Scheme.forgetToLocallyRingedSpace.map g) := sorry

namespace Scheme.Pullback

variable {X Y S : Scheme.{u}}

/-- 01JN: the canonical scheme pullback cone is a pullback after forgetting to locally ringed
spaces. This concrete bridge complements the preservation instance and avoids making downstream
arguments reconstruct the chosen pullback object. -/
@[stacks 01JN "canonical pullback in locally ringed spaces"]
theorem isPullback_toLocallyRingedSpace (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback
      (Scheme.forgetToLocallyRingedSpace.map (pullback.fst f g))
      (Scheme.forgetToLocallyRingedSpace.map (pullback.snd f g))
      (Scheme.forgetToLocallyRingedSpace.map f)
      (Scheme.forgetToLocallyRingedSpace.map g) := sorry

end Scheme.Pullback

#synth PreservesLimitsOfShape WalkingCospan
  Scheme.forgetToLocallyRingedSpace

end AlgebraicGeometry
