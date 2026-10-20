module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk.Neighborhood
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

universe u

/- Lemma 66.29.4: for a quasi-coherent module on an algebraic space, the canonical comparison
from the Zariski stalk on a scheme étale neighbourhood, extended to the geometric étale local
ring, to the geometric module stalk is an isomorphism. -/
@[stacks 05VP] #check (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackStalkTensorHom_isIso :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    (F : X.Modules) → [F.IsQuasicoherent] →
    (xbar : GeometricPoint X) → (N : SmallEtaleNeighborhood xbar) →
    IsIso (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackStalkTensorHom F N))
