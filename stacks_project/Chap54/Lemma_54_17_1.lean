/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.SurfaceFactorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 54.17.1: a proper birational morphism between integral Noetherian regular
schemes of dimension `2` is a finite sequence of blowups at closed points, up to an
endpoint isomorphism. -/
@[stacks 0C5R] #check (AlgebraicGeometry.Scheme.Hom.exists_pointBlowupSequence :
  ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [IsIntegral X] [IsIntegral Y] [Scheme.Regular X] [Scheme.Regular Y] (f : X ⟶ Y)
    [IsProper f] [IsBirational f] (hX_dim : topologicalKrullDim X = 2)
    (hY_dim : topologicalKrullDim Y = 2),
    ∃ (Xn : Scheme.{u}) (s : Scheme.PointBlowupSequence Y Xn) (e : X ≅ Xn),
      e.hom ≫ s.toSource = f)

end AlgebraicGeometry.Scheme.Hom
