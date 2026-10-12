/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Nagata
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/- Theorem 38.33.8: a separated finite-type morphism to a quasi-compact and
quasi-separated scheme admits a compactification over the base. -/
@[stacks 0F41] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.nonempty_of_finiteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [CompactSpace S] [QuasiSeparatedSpace S]
      [Scheme.Hom.FiniteType f] [IsSeparated f],
      Nonempty (Of S (Over.mk f)))

end AlgebraicGeometry.Scheme.Compactification
