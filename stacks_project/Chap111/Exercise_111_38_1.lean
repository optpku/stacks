/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineLine.GenericPoint
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

/- Exercise 111.38.1: every morphism from the generic point of the affine line to a finite-type
scheme over a field extends to a principal open subscheme of the affine line. -/
@[stacks 0DJ1] #check
  (AlgebraicGeometry.Scheme.exists_hom_from_ratFunc :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (sX : X ⟶ Spec (.of k))
      [AlgebraicGeometry.QuasiCompact sX]
      [AlgebraicGeometry.LocallyOfFiniteType sX]
      (φ : Spec (.of (RatFunc k)) ⟶ X),
      φ ≫ sX =
          Spec.map
            (CommRingCat.ofHom (algebraMap k (RatFunc k))) →
        ∃ (f : Polynomial k) (hf : f ≠ 0)
          (ψ : Spec (.of (Localization.Away f)) ⟶ X),
          ψ ≫ sX =
              Spec.map
                  (CommRingCat.ofHom
                    (algebraMap (Polynomial k) (Localization.Away f))) ≫
                Spec.map
                  (CommRingCat.ofHom (algebraMap k (Polynomial k))) ∧
            φ = Spec.map
                  (CommRingCat.ofHom (RatFunc.fromAway hf)) ≫ ψ)
