module

public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Stalk
public import ReasLib.Topology.KrullDimension.Local
import StacksCheckRecall

@[expose] public section

universe u

variable (X : AlgebraicGeometry.Scheme.{u})

/- Lemma 28.10.2: the dimension of a scheme is both the supremum of the dimensions of its local
rings and the supremum of its local topological dimensions. -/
@[stacks 04MU] #check
  (AlgebraicGeometry.Scheme.topologicalKrullDim_eq_iSup_ringKrullDim_stalk X :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x))

#check
  (topologicalKrullDim_eq_iSup_topologicalKrullDimAt (X := X) :
    topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt x)
