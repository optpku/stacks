/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FormalModification
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Definition 88.24.1: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism
of locally Noetherian formal algebraic spaces over `S`. The morphism `f` is a
formal modification if it is proper in the sense of Formal Spaces,
Definition 87.31.1 (representable by algebraic spaces, with
`AlgebraicSpace.Proper` Yoneda pullbacks), rig-étale (`RigEtale`), and
rig-surjective (`RigSurjective`), and the relative diagonal
`Δ_f : X ⟶ X ×_Y X`, encoded as `pullback.diagonal f : X ⟶ pullback f f`, is
rig-surjective. -/
@[stacks 0GDK] #check (AlgebraicGeometry.FormalAlgebraicSpace.FormalModification :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f], Prop)
