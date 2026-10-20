/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Remark 90.22.3 (1): if `(U, R, s, t, c)` is a groupoid in functors on
`ArtinianLocalAlgCat Λ k`, there is a canonical isomorphism
`restrictInclusion (completion G) ≅ G`. -/
@[stacks 06KF] #check
  (CategoryTheory.GroupoidInFunctors.restrictInclusionCompletionIso :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      (G : CategoryTheory.GroupoidInFunctors.{u + 1, u, u}
        (ArtinianLocalAlgCat Λ k)),
      CategoryTheory.GroupoidInFunctors.Iso (CategoryTheory.GroupoidInFunctors.restrictInclusion
        (CategoryTheory.GroupoidInFunctors.completion G)) G)

/- Remark 90.22.3 (2): if `(U, R, s, t, c)` is a groupoid in functors on
`CompleteLocalAlgCat Λ k` whose object and arrow functors preserve limits, for
example if they are representable, there is a canonical isomorphism
`completion (restrictInclusion G) ≅ G`. -/
@[stacks 06KF] #check
  (CategoryTheory.GroupoidInFunctors.completionRestrictInclusionIso :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      (G : CategoryTheory.GroupoidInFunctors.{u + 1, u, u}
        (CompleteLocalAlgCat Λ k))
      [CategoryTheory.Limits.PreservesLimits G.U]
      [CategoryTheory.Limits.PreservesLimits G.R],
      CategoryTheory.GroupoidInFunctors.Iso (CategoryTheory.GroupoidInFunctors.completion
        (CategoryTheory.GroupoidInFunctors.restrictInclusion G)) G)
