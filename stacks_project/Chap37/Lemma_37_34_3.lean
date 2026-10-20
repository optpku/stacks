/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Module.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/- Lemma 37.34.3: an affine finitely presented morphism `f : X ⟶ S` and a finitely
presented module `ℱ` on `X` that is flat over `S` admit a finite-type approximation
diagram with a coherent module `ℱ₀` flat over the finite-stage base `S₀`, whose
pullback along `D.toW` is isomorphic to `ℱ`. -/
@[stacks 05FD] #check
  (AlgebraicGeometry.FiniteTypeApproximationDiagram.exists_isPullback_with_coherent_flatOver :
    ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
      (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom],
      ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
        (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
        (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
        (_ : Scheme.Hom.FiniteType D.toSi) (ℱ₀ : D.W.Modules) (_ : ℱ₀.IsCoherent)
        (_ : SheafOfModules.IsFlatOver ℱ₀ D.toSi.toShHom),
        IsPullback D.toW f D.toSi π ∧
          Nonempty ((Scheme.Modules.pullback D.toW).obj ℱ₀ ≅ ℱ))

end AlgebraicGeometry.FiniteTypeApproximationDiagram
