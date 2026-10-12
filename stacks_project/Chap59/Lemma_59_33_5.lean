/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf.LocallyRinged
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
noncomputable section

universe u

/- Lemma 59.33.5: for every scheme, the small étale site with its structure
   sheaf is locally ringed. -/
@[stacks 04HZ] #check (AlgebraicGeometry.Scheme.AssociatedModule.smallCommStructureSheaf_etale_isLocallyRinged : ∀ (S : AlgebraicGeometry.Scheme.{u}), (AlgebraicGeometry.Scheme.AssociatedModule.smallCommStructureSheaf .etale S).IsLocallyRinged)
