module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.Topology.Catenary
public import ReasLib.Topology.KrullDimension.Local

@[expose] public section

universe u

open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Lemma 107.5.13 (1): if `X` is an irreducible Jacobson catenary locally Noetherian scheme of
finite dimension, then `topologicalKrullDim U = topologicalKrullDim X` for every nonempty open
`U ⊆ X`. -/
@[stacks 0DRT]
theorem topologicalKrullDim_open_eq_of_irreducible
    (X : Scheme.{u}) [IrreducibleSpace X] [JacobsonSpace X] [CatenarySpace X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X < ⊤)
    (U : X.Opens) (hU : Nonempty U) :
    topologicalKrullDim U = topologicalKrullDim X := sorry

/-- Lemma 107.5.13 (2): if `X` is an irreducible Jacobson catenary locally Noetherian scheme of
finite dimension, then `topologicalKrullDimAt x` equals `topologicalKrullDim X` at every point
`x : X`. -/
@[stacks 0DRT]
theorem topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
    (X : Scheme.{u}) [IrreducibleSpace X] [JacobsonSpace X] [CatenarySpace X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X < ⊤) (x : X) :
    topologicalKrullDim X = topologicalKrullDimAt x := sorry

/-- On an irreducible Jacobson catenary locally Noetherian scheme of finite dimension, local
topological Krull dimension is independent of the point. -/
theorem topologicalKrullDimAt_eq
    (X : Scheme.{u}) [IrreducibleSpace X] [JacobsonSpace X] [CatenarySpace X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X < ⊤) (x y : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt y := sorry

end AlgebraicGeometry.Scheme
