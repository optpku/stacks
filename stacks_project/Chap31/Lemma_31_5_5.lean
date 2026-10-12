/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Zero
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory.Limits

universe u

/- Lemma 31.5.5: for every quasicoherent module ℱ on a scheme X, ℱ is zero if
and only if its weakly associated locus is empty. -/
@[stacks 05AP] #check
  (AlgebraicGeometry.Scheme.Modules.isZero_iff_weakAss_eq_empty :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      IsZero ℱ ↔ ℱ.weakAss = (∅ : Set X))
