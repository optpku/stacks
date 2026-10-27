/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.Hull

/-! # Hulls and prorepresentability of algebraic-space deformations -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))
variable [AlgebraicSpace.Proper
  (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase X)]
  [ArtinianLocalAlgCat.IsClassical Λ k]

/- Lemma 93.11.5 (1). Over a classical complete local base, the functor of
isomorphism classes of deformations of a proper algebraic space has a hull. -/
@[stacks 0ET7] #check
  (FlatAlgebraicSpaceCat.exists_isHull_isoClass Λ k X :
    ∃ R : CompleteLocalAlgCat Λ k,
      ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
          FlatAlgebraicSpaceCat.isoClassFunctor Λ k X,
        NatTrans.IsSmooth η ∧
          Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)))

variable (h_der : Subsingleton
  (AlgebraicGeometry.AlgebraicSpace.Hom.derivations
    (FlatAlgebraicSpaceCat.ofResidue Λ k X).structureHom
    (SheafOfModules.unit
      (structureSheaf (FlatAlgebraicSpaceCat.ofResidue Λ k X).space))))

/- Lemma 93.11.5 (2). With the same properness and classical assumptions, vanishing
k-derivations of the structure sheaf imply that the functor is prorepresentable. -/
@[stacks 0ET7] #check
  (FlatAlgebraicSpaceCat.isProrepresentable_isoClass Λ k X h_der :
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        (CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ≅
          FlatAlgebraicSpaceCat.isoClassFunctor Λ k X))
