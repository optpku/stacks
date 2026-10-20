/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.MinimalVersal
import StacksCheckRecall

open CategoryTheory CompleteLocalAlgCat ArtinianLocalAlgCat
open CofiberedCategoryOver.Groupoids Functor
open CategoryTheory.GroupoidInFunctors
open scoped BasedFunctor

universe u

/- Lemma 90.27.6. A deformation category with finite-dimensional tangent and
infinitesimal-automorphism spaces has a minimal versal formal object whose
kernel-pair groupoid is minimal, smooth, and prorepresentable and whose canonical
quotient map is an equivalence. -/
@[stacks 06L2] #check
  (CategoryTheory.GroupoidInFunctors.exists_minimalVersalPresentation :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      {G : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
        (ArtinianLocalAlgCat Λ k)}
      [IsDeformationCategory G.p]
      [FiniteDimensional k ((fiberIsoClassFunctor G.p).obj (dualNumber Λ k))]
      [FiniteDimensional k (infinitesimalAutomorphisms G.p)],
      ∃ ξ : FormalObject
          (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k),
        FormalObject.IsMinimalVersal ξ ∧
          ∃ (hs : IsSmooth (ofFormalObject ξ).s (ofFormalObject ξ).t)
            (hp : IsProrepresentable (ofFormalObject ξ)),
            IsMinimal (ofFormalObject ξ) (smooth := hs) (prorepresentable := hp) ∧
              BasedFunctor.IsEquivalence
                (quotientMap (FormalObject.associatedMorphismOver ξ)))
