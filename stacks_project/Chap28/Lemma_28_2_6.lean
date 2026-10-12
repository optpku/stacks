/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.Retrocompact
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open Topology

universe u

/-
Lemma 28.2.6: Let `X` be a scheme. A subset `E` of `X` is retrocompact in `X` if and only if
`E ∩ U` is quasi-compact for every affine open `U` of `X`.
-/
@[stacks 07ZL] #check
  (AlgebraicGeometry.Scheme.isRetrocompact_iff_forall_isAffineOpen :
    ∀ {X : Scheme.{u}} {E : Set X},
      IsRetrocompact E ↔ ∀ U : X.Opens, IsAffineOpen U → IsCompact (E ∩ U))
