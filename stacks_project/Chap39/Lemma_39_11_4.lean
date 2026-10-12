/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.RepresentableTorsor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 39.11.4: For any standard topology `τ`, a group-scheme action is a torsor
for the standard precoverage if and only if its represented action is a torsor on
the corresponding site over the base scheme. -/
@[stacks 049B]
#check (AlgebraicGeometry.GroupScheme.isStandardTorsor_iff_isSheafTorsor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (τ : AlgebraicGeometry.StandardTopology)
    (G : Grp (Over S)) (X : Mod (Over S) G.X),
    AlgebraicGeometry.GroupScheme.IsStandardTorsor G X τ ↔
      AlgebraicGeometry.GroupScheme.IsSheafTorsor τ G X)
