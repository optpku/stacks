/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.AffineOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.45.1: every finite set of points in the source of a separated, locally
quasi-finite morphism to an affine scheme is contained in a single affine open. -/
@[stacks 07S0] #check
  (AlgebraicGeometry.Scheme.Hom.exists_affineOpen_containing_finiteSet :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      [LocallyQuasiFinite f] [IsAffine Y] (E : Set X), E.Finite →
        ∃ U : X.affineOpens, E ⊆ ((U : X.Opens) : Set X))

end AlgebraicGeometry.Scheme.Hom
