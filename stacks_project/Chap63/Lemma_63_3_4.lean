/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 63.3.4: For a proper scheme morphism `f : X ⟶ Y`, the equality
`f_! = f_*` is formalized by the canonical natural isomorphism from
compact-support direct image to ordinary small-étale pushforward. -/
@[stacks 0F51] #check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
    AlgebraicGeometry.Scheme.Etale.etaleLowerShriek f ≅
      AlgebraicGeometry.Scheme.etaleAbelianPushforward f)
