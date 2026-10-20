module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Spectral
import StacksCheckRecall

/-!
# Spectral spaces of quasi-compact quasi-separated algebraic spaces

The space of points of a quasi-compact, absolutely quasi-separated algebraic space is spectral.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.15.2: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Then the topological space `Points X` is a spectral space. -/
@[stacks 0A4G] #check (AlgebraicGeometry.AlgebraicSpace.instSpectralSpacePoints :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact X]
    [AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated X],
    SpectralSpace (AlgebraicGeometry.AlgebraicSpace.Points X))

end AlgebraicGeometry.AlgebraicSpace
