/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Functor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.13.5: finite-dimensionality of the canonical tangent space is
Schlessinger's (H3). Conditions (H1) and (H2) correspond to (S1) and (S2), as in
Remark 90.10.3. Together they imply existence of a versal formal object of the
associated cofibered set. The link with hulls in Remark 90.15.6 is a forward
reference. -/
@[stacks 0D3G] #check (CategoryTheory.Functor.exists_isVersal_pi :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [Functor.IsPredeformationFunctor F] [Functor.HasSchlessingerH1 F]
    [Functor.HasSchlessingerH2 F]
    [FiniteDimensional k (Functor.IsPredeformationFunctor.tangentSpace F)],
    ∃ ξ : FormalObject (FormalObject.elementsProjectionULift F),
      FormalObject.IsVersal ξ)
