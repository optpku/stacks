/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.AffineEtale
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 66.6.3: let `S` be a scheme. Let `X` be an algebraic space over `S`. Then `X` is
quasi-compact if and only if there exists an étale surjective morphism `U ⟶ X` with `U` an
affine scheme. -/
@[stacks 03H6] #check (AlgebraicGeometry.AlgebraicSpace.isQuasiCompact_iff_exists_affineEtale :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact X ↔
      ∃ (U : CategoryTheory.Over S) (f : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ X),
        (CategoryTheory.MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f ∧
          CategoryTheory.Presheaf.IsLocallySurjective
            (AlgebraicGeometry.Scheme.etaleTopology.over S) f ∧
              AlgebraicGeometry.IsAffine U.left)
