/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface.Line
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.Hypersurface
open AlgebraicGeometry.Scheme.Modules.Intersection
open scoped AlgebraicGeometry

universe u

/- Exercise 111.61.7: The self-intersection of a line on a smooth degree-`d`
hypersurface in projective three-space over an algebraically closed field is `2 - d`. -/
@[stacks 0ELM] #check (AlgebraicGeometry.ProjectiveSpace.Hypersurface.selfNumber_line_eq :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin (3 + 1)) k) (hF : F ∈ grading k 3 d)
    (hFne : F ≠ 0) (hd : 0 < d) [Smooth (hom 3 d F hF)]
    (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k)
    (hL : ∀ i, ℓL i ∈ grading k 3 1)
    (hLindep : LinearIndependent k ℓL)
    (hcontained : containsLine F ℓL hL)
    [HasExt (Sheaf (Opens.grothendieckTopology
      (⊥ : (scheme 3 d F hF).IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})],
    selfNumber k (hom 3 d F hF) ⊥
      (hypersurface_topologicalKrullDim_eq_two d F hF hFne hd)
      (lineAssociatedSheaf d F hF hFne hd ℓL hL hLindep hcontained) =
      (2 : ℚ) - d)
