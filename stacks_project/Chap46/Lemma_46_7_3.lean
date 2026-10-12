/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AffineEquivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Lemma 46.7.3 (1): for `U = Spec A`, the inclusion of adequate module sheaves
into all module sheaves on the big `τ`-site of `U` has a right adjoint. -/
@[stacks 06ZS] #check
  (SheafOfModules.AffineAdeq.inclusionIsLeftAdjoint :
    ∀ (τ : StandardTopology) (A : CommRingCat.{u}),
      (SheafOfModules.AffineAdeq.inclusion τ A).IsLeftAdjoint)

/- Lemma 46.7.3 (2): the counit from the right adjoint back to an adequate
module sheaf is an isomorphism. -/
@[stacks 06ZS] #check
  (SheafOfModules.AffineAdeq.inclusionCounitAppIsIso :
    ∀ (τ : StandardTopology) (A : CommRingCat.{u})
      (ℱ : SheafOfModules.AffineAdeq τ A),
      IsIso ((Adjunction.ofIsLeftAdjoint
        (SheafOfModules.AffineAdeq.inclusion τ A)).counit.app
          ((SheafOfModules.AffineAdeq.inclusion τ A).obj ℱ)))
