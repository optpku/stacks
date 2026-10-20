/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Etale
import StacksCheckRecall

/-!
# Étale criterion for the finite-part functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/- Lemma 79.12.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Suppose that `U` is a scheme, `U ⟶ Y` is an étale
morphism and `Z ⊂ U ×_Y X` is an open subspace finite over `U`. Then the
induced morphism `U ⟶ (X/Y)_fin` is étale. -/
@[stacks 04QE] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.hom_etale :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U : Over S} (a : ofOver U ⟶ Y) [AlgebraicSpace.Etale a]
    (Z : OpenSubspace (pullback a f))
    (hZ : IsFinite (Z.ι ≫ pullback.fst a f)),
    (over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf
      (SubspacePoint.hom (SubspacePoint.of a Z hZ)))

end AlgebraicGeometry.AlgebraicSpace.FinitePart
