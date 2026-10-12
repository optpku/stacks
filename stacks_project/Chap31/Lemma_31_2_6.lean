/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Zero
import StacksCheckRecall

open CategoryTheory.Limits

universe u

/- Lemma 31.2.6: for a quasicoherent module `ℱ` on a locally Noetherian scheme `X`, `ℱ` is zero
if and only if its associated-point set is empty. -/
@[stacks 05AG] #check
  (AlgebraicGeometry.Scheme.Modules.isZero_iff_associatedPoints_eq_empty :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      [AlgebraicGeometry.IsLocallyNoetherian X],
      IsZero ℱ ↔ AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ = (∅ : Set X))

#check
  (AlgebraicGeometry.Scheme.Modules.isZero_iff_forall_not_mem_associatedPoints :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      [AlgebraicGeometry.IsLocallyNoetherian X],
      IsZero ℱ ↔ ∀ x : X, x ∉ AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ)
