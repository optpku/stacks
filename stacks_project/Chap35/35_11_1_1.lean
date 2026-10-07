module

public import stacks_project.Chap35.«35_11_1_1_RingedComparison»
import StacksCheckRecall

@[expose] public section

universe u

/- 35.11.1.1 (1): For the Zariski topology, the canonical morphism goes from
the affine small ringed topos of a scheme to its full small ringed topos. -/
@[stacks 0GZW] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallAffineComparison.comparison :
    (S : AlgebraicGeometry.Scheme.{u}) →
      RingedSite.ToposHom
        (AlgebraicGeometry.Scheme.Zariski.SmallAffineComparison.affineRingedSite S)
        (AlgebraicGeometry.Scheme.Zariski.Small.liftedRingedSite S))

/- 35.11.1.1 (2): For the étale topology, the canonical morphism goes from
the affine small ringed topos of a scheme to its full small ringed topos. -/
@[stacks 0GZW] #check
  (AlgebraicGeometry.Scheme.Etale.SmallAffineComparison.comparison :
    (S : AlgebraicGeometry.Scheme.{u}) →
      RingedSite.ToposHom
        (AlgebraicGeometry.Scheme.Etale.SmallAffineComparison.affineRingedSite S)
        (AlgebraicGeometry.Scheme.Etale.Small.liftedRingedSite S))
