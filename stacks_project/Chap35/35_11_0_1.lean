module

public import stacks_project.Chap35.«35_11_0_1_RingedComparison»
import StacksCheckRecall

@[expose] public section

universe u

/- 35.11.0.1: For the Zariski, étale, smooth, syntomic, or fppf topology,
there is a canonical morphism from the affine standard ringed topos with
`𝒪_Aff` to the corresponding big ringed topos. -/
@[stacks 0GZU] #check
  (AlgebraicGeometry.StandardTopology.Affine.comparison :
    ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u}),
      RingedSite.ToposHom
        (AlgebraicGeometry.StandardTopology.Affine.ringedSite τ S)
        (AlgebraicGeometry.StandardTopology.Big.liftedRingedSite τ S))
