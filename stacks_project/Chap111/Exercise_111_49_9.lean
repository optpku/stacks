module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties
public import stacks_project.Chap111.Exercise_111_49_9_Conic
public import stacks_project.Chap111.Exercise_111_49_9_Line
public import stacks_project.Chap111.Exercise_111_49_9_Quotient
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Exercise 111.49.9 (1): over a field `k`, given a line and a disjoint nonsingular conic in
`ℙ³_k` and an isomorphism `φ` from the line to the conic over `k`, there is a `k`-scheme `X`
obtained by glueing the conic to the line along `φ`. -/
@[stacks 02AS]
theorem exists_lineConicQuotient {k : Type u} [Field k] {L C : Scheme.{u}}
    (iL : L ⟶ scheme k 3) (iC : C ⟶ scheme k 3) [IsLine iL] [IsNonsingularConic iC]
    (h_disjoint : Disjoint (Set.range iL) (Set.range iC)) (φ : L ⟶ C) [IsIso φ]
    (hφ : φ ≫ iC ≫ toSpec k 3 = iL ≫ toSpec k 3) :
    ∃ (X : SchemeOverField k) (π : scheme k 3 ⟶ X.left) (U : X.left.Opens),
      IsLineConicQuotient iL iC φ X π U := sorry

/-- Exercise 111.49.9 (2): over a field `k`, given a line and a disjoint nonsingular conic in
`ℙ³_k` and an isomorphism `φ` from the line to the conic over `k`, there is a proper variety
`X` over `k` obtained by glueing the conic to the line along `φ`. -/
@[stacks 02AS]
theorem exists_lineConicQuotient_properVariety {k : Type u} [Field k] {L C : Scheme.{u}}
    (iL : L ⟶ scheme k 3) (iC : C ⟶ scheme k 3) [IsLine iL] [IsNonsingularConic iC]
    (h_disjoint : Disjoint (Set.range iL) (Set.range iC)) (φ : L ⟶ C) [IsIso φ]
    (hφ : φ ≫ iC ≫ toSpec k 3 = iL ≫ toSpec k 3) :
    ∃ (X : SchemeOverField k) (π : scheme k 3 ⟶ X.left) (U : X.left.Opens),
      IsLineConicQuotient iL iC φ X π U ∧ ProperVariety X := sorry

/-- Exercise 111.49.9 (3): a scheme obtained by glueing a line in `ℙ³_k` to a disjoint
nonsingular conic is not a projective variety over `k`. -/
@[stacks 02AS]
theorem not_projectiveVariety_of_isLineConicQuotient {k : Type u} [Field k]
    {L C : Scheme.{u}} (iL : L ⟶ scheme k 3) (iC : C ⟶ scheme k 3)
    [IsLine iL] [IsNonsingularConic iC]
    (h_disjoint : Disjoint (Set.range iL) (Set.range iC)) (φ : L ⟶ C) [IsIso φ]
    (X : SchemeOverField k) (π : scheme k 3 ⟶ X.left) (U : X.left.Opens)
    (h : IsLineConicQuotient iL iC φ X π U) : ¬ ProjectiveVariety X := sorry

/-- A line-conic identification quotient over a field admits no ample invertible module. -/
theorem not_hasAmpleInvertibleModule_of_isLineConicQuotient {k : Type u} [Field k]
    {L C : Scheme.{u}} (iL : L ⟶ scheme k 3) (iC : C ⟶ scheme k 3)
    [IsLine iL] [IsNonsingularConic iC]
    (h_disjoint : Disjoint (Set.range iL) (Set.range iC)) (φ : L ⟶ C) [IsIso φ]
    (X : SchemeOverField k) (π : scheme k 3 ⟶ X.left) (U : X.left.Opens)
    (h : IsLineConicQuotient iL iC φ X π U) :
    ¬ Scheme.Modules.HasAmpleInvertibleModule X.left := sorry

end AlgebraicGeometry
