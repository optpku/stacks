/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.Topology.Catenary
public import ReasLib.Topology.KrullDimension.Local

@[expose] public section

universe u

open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Every nonempty open subset of an irreducible Jacobson catenary locally Noetherian scheme
of finite dimension has the same topological Krull dimension as the scheme. -/
@[stacks 0DRT]
theorem topologicalKrullDim_open_eq_of_irreducible
    (X : Scheme.{u}) [IrreducibleSpace X] [JacobsonSpace X] [CatenarySpace X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X < ⊤)
    (U : X.Opens) (hU : Nonempty U) :
    topologicalKrullDim U = topologicalKrullDim X := sorry

/-- The global topological Krull dimension of an irreducible Jacobson catenary locally
Noetherian scheme of finite dimension equals its local dimension at every point. -/
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
