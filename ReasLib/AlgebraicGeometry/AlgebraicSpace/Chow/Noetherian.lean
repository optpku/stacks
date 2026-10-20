/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type morphism of algebraic spaces to a Noetherian target
admits a dense open and an admissible blowup that open-immerses into a proper
representable algebraic space over the target. This proper space is an admissible
blowup of a closed subspace of finite-dimensional relative projective space,
with compatible open immersions from the dense open. -/
theorem exists_dense_open_isAdmissibleBlowup_closedImmersion
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Separated f] [IsNoetherian Y] :
    ∃ (U : OpenSubspace X) (n : ℕ) (X' Z' Z : AlgebraicSpace S)
      (bX : X' ⟶ X) (j : X' ⟶ Z') (bZ : Z' ⟶ Z)
      (c : Z ⟶ ProjectiveSpace n Y)
      (ιX' : U.X ⟶ X') (ιZ' : U.X ⟶ Z') (ιZ : U.X ⟶ Z)
      (hιX' : IsOpenImmersion ιX') (hιZ' : IsOpenImmersion ιZ')
      (hιZ : IsOpenImmersion ιZ),
      Dense (U.pointsSet : Set (Points X)) ∧
        IsAdmissibleBlowup U bX ∧ IsOpenImmersion j ∧
        Proper (bZ ≫ c ≫ ProjectiveSpace.toBase n Y) ∧
        yoneda.relativelyRepresentable (bZ ≫ c ≫ ProjectiveSpace.toBase n Y) ∧
        IsAdmissibleBlowup ⟨U.X, ιZ, hιZ⟩ bZ ∧
        IsClosedImmersion c ∧
        ιX' ≫ bX = U.ι ∧ ιX' ≫ j = ιZ' ∧ ιZ' ≫ bZ = ιZ ∧
        ιZ ≫ c ≫ ProjectiveSpace.toBase n Y = U.ι ≫ f ∧
        bX ≫ f = j ≫ bZ ≫ c ≫ ProjectiveSpace.toBase n Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
