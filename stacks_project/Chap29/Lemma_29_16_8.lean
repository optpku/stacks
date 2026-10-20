/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point.Jacobson

open AlgebraicGeometry

universe u

/- Lemma 29.16.8: for a scheme `S`, Jacobsonness is equivalent to its finite-type points being
exactly its closed points, and to closed-point preservation, with finite residue-field extensions,
under every locally finite type morphism to `S`. -/
@[stacks 01TB] #check
  (AlgebraicGeometry.Scheme.jacobsonSpace_tfae_finiteTypePoints :
    ∀ S : Scheme.{u},
      List.TFAE
        [ JacobsonSpace S
        , finiteTypePoints S = closedPoints S
        , ∀ {T : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f],
            Set.MapsTo f (closedPoints T) (closedPoints S)
        , ∀ {T : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f], ∀ t : T,
            t ∈ closedPoints T →
              f t ∈ closedPoints S ∧
                Module.Finite (S.residueField (f t)) (T.residueField t)
        ])
