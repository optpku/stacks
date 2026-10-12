/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Noetherian

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 38.16.5: at a Noetherian target stalk, purity along the fibre is equivalent
to universal purity along that fibre. -/
@[stacks 05J8] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureAlong.iff_universally_of_noetherian_stalk :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S) [f.FiniteType]
      [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
      [IsNoetherianRing (S.presheaf.stalk s)],
      F.IsPureAlong f s ↔ F.IsUniversallyPureAlong f s)
