/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.VersalCriterion
import StacksCheckRecall

/-!
# Versal formal objects under Schlessinger's conditions

A formal object of a predeformation category satisfying (S1) and (S2) is versal
precisely when the induced map on dual-number fibre isomorphism classes is
surjective and every small-extension triangle in the completion admits a
ring-map fill-in on the complete local bases.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Lemma 90.13.2: let `p` be a predeformation category satisfying (S1) and (S2),
and let `ξ` be a formal object of `p` corresponding to a based functor
`φ : CompleteLocalAlgCat.identityProjection ξ.base ⥤ᵇ p`. Then `ξ` is versal if
and only if the induced map on dual-number fibre isomorphism classes is
surjective and `ξ` admits a ring-map fill-in along every small extension
triangle in the completion. -/
@[stacks 06IU] #check (FormalObject.isVersal_iff :
  ∀ [Functor.IsPredeformationCategory p]
    [Functor.HasSchlessingerS1 p] [Functor.HasSchlessingerS2 p] (ξ : FormalObject p)
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p)
    (hφ : Represents ξ φ),
    IsVersal ξ ↔
      Function.Surjective (φ.fiberFunctor (dualNumber Λ k)).isoClassesMap ∧
        ExistsBaseLiftAlongSmallExtension ξ)

end FormalObject
