/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.SimplicialScheme.QCoh.Adjunction

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.SimplicialObject

/- Lemma 85.28.3: let `f : V ⟶ U` be a cartesian morphism of simplicial schemes.
Assume the face morphisms `U.δ j : U _⦋n+1⦌ ⟶ U _⦋n⦌` are flat and the
component morphisms `f.app (op ⦋n⦌) : V _⦋n⦌ ⟶ U _⦋n⦌` are quasi-compact and
quasi-separated. Then `QCoh.pullback f : QCoh U ⥤ QCoh V` and
`QCoh.pushforward f : QCoh V ⥤ QCoh U` form an adjoint pair of functors
between the categories of quasi-coherent modules on the simplicial Zariski
sites of `U` and `V`. -/
@[stacks 07TK] #check
  (AlgebraicGeometry.SimplicialObject.QCoh.pullbackPushforwardAdjunction :
    ∀ {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
      [CategoryTheory.SimplicialObject.IsCartesian f]
      [∀ (n : ℕ) (j : Fin (n + 2)), Flat (U.δ j)]
      [∀ (n : ℕ), QuasiCompact (f.app (op ⦋n⦌))]
      [∀ (n : ℕ), QuasiSeparated (f.app (op ⦋n⦌))],
      (QCoh.pullback f : QCoh U ⥤ QCoh V) ⊣
        (QCoh.pushforward f : QCoh V ⥤ QCoh U))

end AlgebraicGeometry.SimplicialObject
