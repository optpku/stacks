module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Homeomorph.Defs
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.UnramifiedComparison

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Proposition 64.27.3: for an integral normal Noetherian scheme `X` and an algebraic
geometric point `ηbar` lying over `genericPoint X`, the étale fundamental group
`etaleFundamentalGroup X ηbar` is identified with `Gal(M / X.functionField)`, where
`M = maximalUnramifiedExtension X hX` is the maximal extension of the function field
`k(X) = X.functionField` inside a separable closure such that the normalization of `X`
in every finite subextension is finite étale over `X`. The identification is the
homeomorphism of topological groups `etaleFundamentalGroupToUnramifiedGalois`. -/
@[stacks 03VG] #check
  (AlgebraicGeometry.Scheme.etaleFundamentalGroup_isHomeomorph_unramifiedGalois :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] (hX : X.isNormal)
      (ηbar : GeometricPoint X)
      (h_alg : @IsAlgClosure _ _ _ _ (ηbar.toFieldValuedPoint.residueFieldHom.hom.toAlgebra) _)
      (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X),
      IsHomeomorph (AlgebraicGeometry.Scheme.etaleFundamentalGroupToUnramifiedGalois
        hX ηbar h_alg h_gen))
