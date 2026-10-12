/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinePlaneExt

@[expose] public section

open AlgebraicGeometry.ProjectiveSpace CategoryTheory CategoryTheory.Abelian

universe u

/- Exercise 111.48.1 (1): global Ext from the structure sheaf of a line to that of a
containing plane in projective three-space has dimensions two and three in degrees one and
two, and zero in every other degree. -/
@[stacks 0DD1] #check
  (AlgebraicGeometry.ProjectiveSpace.finrank_ext_line_plane_of_contained :
    ∀ {k : Type u} [Field k]
      (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k)
      (ℓP : MvPolynomial (Fin (3 + 1)) k)
      (hL : ∀ i, ℓL i ∈ grading k 3 1) (hP : ℓP ∈ grading k 3 1)
      (hPne : ℓP ≠ 0) (hLindep : LinearIndependent k ℓL)
      (hsub : lineContainedInPlane ℓL ℓP) [HasExt (scheme k 3).Modules] (i : ℕ),
      Module.finrank k (Ext (lineModule ℓL hL) (planeModule ℓP hP) i) =
        if i = 1 then 2 else if i = 2 then 3 else 0)

/- Exercise 111.48.1 (2): global Ext from the structure sheaf of a line to that of a
plane not containing it in projective three-space has dimension one in degree two and zero
in every other degree. -/
@[stacks 0DD1] #check
  (AlgebraicGeometry.ProjectiveSpace.finrank_ext_line_plane_of_not_contained :
    ∀ {k : Type u} [Field k]
      (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k)
      (ℓP : MvPolynomial (Fin (3 + 1)) k)
      (hL : ∀ i, ℓL i ∈ grading k 3 1) (hP : ℓP ∈ grading k 3 1)
      (hPne : ℓP ≠ 0) (hLindep : LinearIndependent k ℓL)
      (hnot : ¬ lineContainedInPlane ℓL ℓP) [HasExt (scheme k 3).Modules] (i : ℕ),
      Module.finrank k (Ext (lineModule ℓL hL) (planeModule ℓP hP) i) =
        if i = 2 then 1 else 0)
