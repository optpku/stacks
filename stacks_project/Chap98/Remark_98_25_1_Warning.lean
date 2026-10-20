module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian
import StacksCheckRecall

/-!
# The Noetherian site does not have fibre products

The site `(Noetherian/S)_τ` does not have fibre products over a nonempty
locally Noetherian base. Its continuous inclusion into `(Sch/S)_τ` need not
define a morphism of sites in general: the fppf example over `Spec (ZMod p)`
for a prime `p` shows that the associated sheaf pullback is not left exact.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty CategoryTheory.Limits

universe u

/- Remark 98.25.1 (Warning) (1): the site `(Noetherian/S)_τ` does not have
fibre products. -/
@[stacks 0GE2] #check
  (AlgebraicGeometry.not_hasPullbacks_locallyNoetherian :
    ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] [Nonempty S],
      ¬ HasPullbacks (AlgebraicGeometry.Scheme.Over.locallyNoetherian S).FullSubcategory)

/- Remark 98.25.1 (Warning) (2): the continuous inclusion
`(Noetherian/S)_τ ⥤ (Sch/S)_τ` need not define a morphism of sites in general.
The prime-field fppf example in Examples, Section 110.60 witnesses failure
of left exactness of the associated sheaf pullback. -/
@[stacks 0GE2] #check
  (AlgebraicGeometry.not_preservesFiniteLimits_locallyNoetherianInclusion_fppf :
    ∀ (p : ℕ) [Fact p.Prime],
      let base := Spec (CommRingCat.of (ZMod p))
      let noetherian : ObjectProperty (Over base) :=
        fun object => IsLocallyNoetherian object.left
      let topology := Scheme.fppfTopology.over base
      ¬ PreservesFiniteLimits
        (noetherian.ι.sheafPullback (Type 1)
          (noetherian.ι.restrictedTopology topology) topology))
