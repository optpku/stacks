/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
