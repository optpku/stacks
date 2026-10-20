/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative

/-!
# Segre embeddings

This file records the existence of the relative Segre embedding for chosen models of projective
space over a scheme.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOver

/-- The fibre product of chosen relative projective spaces of dimensions `n` and `m` admits a
closed immersion over the base into a chosen relative projective space of dimension
`n * m + n + m`. -/
@[stacks 01WD]
theorem exists_segreEmbedding {S : Scheme.{u}} {n m : ℕ}
    (P : ProjectiveSpaceOver S n) (Q : ProjectiveSpaceOver S m) :
    ∃ (R : ProjectiveSpaceOver S (n * m + n + m))
      (i : pullback P.hom Q.hom ⟶ R.scheme),
      IsClosedImmersion i ∧
        i ≫ R.hom = pullback.fst P.hom Q.hom ≫ P.hom := sorry

end AlgebraicGeometry.ProjectiveSpaceOver
