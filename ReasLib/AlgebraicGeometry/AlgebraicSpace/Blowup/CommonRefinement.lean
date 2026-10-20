/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-! # Common refinements of admissible blowups of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite family of blowups admissible over a quasi-compact open subspace of
a quasi-compact quasi-separated algebraic space has a common admissible
refinement, and every comparison morphism is admissible over the corresponding
inverse-image open subspace. -/
theorem exists_isAdmissibleBlowup_common_refinement
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U : OpenSubspace X) [QuasiCompact U.ι]
    {n : ℕ} (Xi : Fin n → AlgebraicSpace S)
    (bi : ∀ i : Fin n, Xi i ⟶ X)
    (hbi : ∀ i : Fin n, IsAdmissibleBlowup U (bi i)) :
    ∃ (X' : AlgebraicSpace S) (b : X' ⟶ X),
      IsAdmissibleBlowup U b ∧
        ∀ i : Fin n, ∃ c : X' ⟶ Xi i,
          c ≫ bi i = b ∧ IsAdmissibleBlowup (U.inverseImage (bi i)) c :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
