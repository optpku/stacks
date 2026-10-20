module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian
import StacksCheckRecall

/-!
# The Noetherian fppf site over Spec(F_p)

The inclusion of the fppf site of locally Noetherian schemes over
`Spec (ZMod p)` into the big fppf site does not define a morphism of sites.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty CategoryTheory.Limits

/- Lemma 110.60.1: with `S = Spec (ZMod p)`, the inclusion functor of the
fppf site of locally Noetherian schemes over `S` into `(Sch/S)_fppf` does not
define a morphism of sites: its left adjoint on set-valued sheaves is not
left exact. -/
@[stacks 0GE9] #check
  (AlgebraicGeometry.not_preservesFiniteLimits_locallyNoetherianInclusion_fppf :
    ∀ (p : ℕ) [Fact p.Prime],
      let base := Spec (CommRingCat.of (ZMod p))
      let noetherian : ObjectProperty (Over base) :=
        fun object => IsLocallyNoetherian object.left
      let topology := Scheme.fppfTopology.over base
      ¬ PreservesFiniteLimits
        (noetherian.ι.sheafPullback (Type 1)
          (noetherian.ι.restrictedTopology topology) topology))
