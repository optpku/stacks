/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Topology.Retrocompact
import StacksCheckRecall

universe u

/- Lemma 28.24.1: for an open subset `U` of a quasi-compact quasi-separated scheme `X`,
retrocompactness, quasi-compactness, finite affine-open coverability, and being the complement of
the support of finite-type ideal-sheaf data are equivalent. -/
@[stacks 01PH] #check
  (AlgebraicGeometry.Scheme.retrocompactOpen_tfae :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (U : X.Opens),
      List.TFAE [
        IsRetrocompact (U : Set X),
        IsCompact (U : Set X),
        ∃ s : Set X.affineOpens, s.Finite ∧ U = ⨆ V ∈ s, (V : X.Opens),
        ∃ I : X.IdealSheafData,
          I.IsFiniteType ∧ I.support = U.compl
      ])
