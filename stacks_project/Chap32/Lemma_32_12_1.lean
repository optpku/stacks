/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Qcqs

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 32.12.1: if `S` is quasi-compact and quasi-separated and `f : X ⟶ S` is separated
and of finite type, then there is a scheme `X'` immersed into a relative projective space over
`S` together with a proper surjective morphism `X' ⟶ X` compatible over `S`. -/
@[stacks 0202] #check
  (AlgebraicGeometry.ChowLemmaQcqsModification.exists_of_separated_finiteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
      [IsSeparated f] [Scheme.Hom.FiniteType f],
      Nonempty (AlgebraicGeometry.ChowLemmaQcqsModification f))
