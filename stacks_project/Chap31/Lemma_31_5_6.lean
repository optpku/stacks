/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Sections
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.5.6: for a quasicoherent module on a scheme, restriction to an open containing every
weakly associated point is injective. -/
@[stacks 0B3M] #check
  (AlgebraicGeometry.Scheme.Modules.injective_restrictionToOpen_of_weakAss_subset :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (U : X.Opens), ℱ.weakAss ⊆ (U : Set X) →
        Function.Injective (ℱ.val.map (TopologicalSpace.Opens.leTop U).op))
