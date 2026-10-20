/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Constancy
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry TopologicalSpace

/- Lemma 107.5.13 (1): if `X` is an irreducible Jacobson catenary locally Noetherian scheme of
finite dimension, then `topologicalKrullDim U = topologicalKrullDim X` for every nonempty open
`U ⊆ X`. -/
@[stacks 0DRT]
#check (AlgebraicGeometry.Scheme.topologicalKrullDim_open_eq_of_irreducible :
    ∀ (X : Scheme.{u}) [IrreducibleSpace X] [JacobsonSpace X] [CatenarySpace X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X < ⊤)
    (U : X.Opens) (hU : Nonempty U),
    topologicalKrullDim U = topologicalKrullDim X)

/- Lemma 107.5.13 (2): if `X` is an irreducible Jacobson catenary locally Noetherian scheme of
finite dimension, then `topologicalKrullDimAt x` equals `topologicalKrullDim X` at every point
`x : X`. -/
@[stacks 0DRT]
#check (AlgebraicGeometry.Scheme.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible :
    ∀ (X : Scheme.{u}) [IrreducibleSpace X] [JacobsonSpace X] [CatenarySpace X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X < ⊤) (x : X),
    topologicalKrullDim X = topologicalKrullDimAt x)

/- On an irreducible Jacobson catenary locally Noetherian scheme of finite dimension, local
topological Krull dimension is independent of the point. -/
#check (AlgebraicGeometry.Scheme.topologicalKrullDimAt_eq :
    ∀ (X : Scheme.{u}) [IrreducibleSpace X] [JacobsonSpace X] [CatenarySpace X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X < ⊤) (x y : X),
    topologicalKrullDimAt x = topologicalKrullDimAt y)
