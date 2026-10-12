/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Noetherian open subschemes

This file records the stability of Noetherian schemes under restriction to an open subset.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- An open subscheme of a Noetherian scheme is Noetherian. -/
instance instIsNoetherianRestrictOfIsNoetherian {X : Scheme.{u}}
    [IsNoetherian X] (U : X.Opens) :
    IsNoetherian (X.restrict U.isOpenEmbedding) := by
  change IsNoetherian U.toScheme
  exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstanceAs (CompactSpace (U : Set X)) }

/-- The open-scheme presentation of a Noetherian restriction is Noetherian. -/
instance instIsNoetherianRestrictOfIsNoetherian_toScheme {X : Scheme.{u}}
    [IsNoetherian X] (U : X.Opens) : IsNoetherian U.toScheme :=
  instIsNoetherianRestrictOfIsNoetherian U

end AlgebraicGeometry.Scheme
