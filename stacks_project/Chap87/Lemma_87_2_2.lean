/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import stacks_project.Chap03.Lemma_3_9_2_ObjectProperty
public import stacks_project.Chap87.Lemma_87_2_1_FunctorOfPoints

/-!
# Lemma 87.2.2

The functor of points of a formal scheme is a sheaf for the fpqc topology.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.FormalScheme

/-- Lemma 87.2.2. Let `X` be a formal scheme. The functor of points
`h_X := (functorOfPoints P).obj X` from Lemma 87.2.1, evaluated on a
category of schemes `Sch_α` encoded by `Scheme.IsSmallBoundClosed P`,
satisfies the sheaf condition for fpqc coverings, as a sheaf for
`P.ι.restrictedTopology Scheme.fpqcTopology`. -/
@[stacks 0AI2]
theorem functorOfPoints_isSheaf_fpqc {P : ObjectProperty Scheme.{u}}
    (hP : Scheme.IsSmallBoundClosed P) (X : FormalScheme.{u}) :
    Presheaf.IsSheaf (P.ι.restrictedTopology Scheme.fpqcTopology)
      ((functorOfPoints P).obj X) :=
  sorry

/-- The unrestricted functor of points of a formal scheme `X`, sending a scheme
`S` to morphisms `toFormalScheme.obj S ⟶ X`, is a sheaf for
`Scheme.fpqcTopology`. -/
theorem isSheaf_fpqc (X : FormalScheme.{u}) :
    Presheaf.IsSheaf Scheme.fpqcTopology
      (Scheme.toFormalScheme.op ⋙ yoneda.obj X) :=
  sorry

/-- The unrestricted functor of points of a formal scheme `X` is a sheaf for
`Scheme.fppfTopology`. -/
theorem isSheaf_fppf (X : FormalScheme.{u}) :
    Presheaf.IsSheaf Scheme.fppfTopology
      (Scheme.toFormalScheme.op ⋙ yoneda.obj X) :=
  sorry

end AlgebraicGeometry.FormalScheme
