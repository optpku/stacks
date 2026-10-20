module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LineConic
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.LineConicQuotient.Results
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open scoped AlgebraicGeometry

universe u

/- Exercise 111.49.9 (1): identifying a line with a disjoint isomorphic nonsingular conic
in projective 3-space gives a scheme over the field. -/
@[stacks 02AS] #check (AlgebraicGeometry.exists_lineConicQuotient :
    ∀ {k : Type u} [Field k] {L C : Scheme.{u}}
    (iL : L ⟶ scheme k 3) (iC : C ⟶ scheme k 3) [IsLine iL] [IsNonsingularConic iC]
    (h_disjoint : Disjoint (Set.range iL) (Set.range iC)) (φ : L ⟶ C) [IsIso φ]
    (hφ : φ ≫ iC ≫ toSpec k 3 = iL ≫ toSpec k 3),
    ∃ (X : SchemeOverField k) (π : scheme k 3 ⟶ X.left) (U : X.left.Opens),
      IsLineConicQuotient iL iC φ X π U)

/- Exercise 111.49.9 (2): the line-conic identification quotient exists as a proper variety. -/
@[stacks 02AS] #check (AlgebraicGeometry.exists_lineConicQuotient_properVariety :
    ∀ {k : Type u} [Field k] {L C : Scheme.{u}}
    (iL : L ⟶ scheme k 3) (iC : C ⟶ scheme k 3) [IsLine iL] [IsNonsingularConic iC]
    (h_disjoint : Disjoint (Set.range iL) (Set.range iC)) (φ : L ⟶ C) [IsIso φ]
    (hφ : φ ≫ iC ≫ toSpec k 3 = iL ≫ toSpec k 3),
    ∃ (X : SchemeOverField k) (π : scheme k 3 ⟶ X.left) (U : X.left.Opens),
      IsLineConicQuotient iL iC φ X π U ∧ ProperVariety X)

/- Exercise 111.49.9 (3): a line-conic identification quotient is not a projective variety. -/
@[stacks 02AS] #check (AlgebraicGeometry.not_projectiveVariety_of_isLineConicQuotient :
    ∀ {k : Type u} [Field k]
    {L C : Scheme.{u}} (iL : L ⟶ scheme k 3) (iC : C ⟶ scheme k 3)
    [IsLine iL] [IsNonsingularConic iC]
    (h_disjoint : Disjoint (Set.range iL) (Set.range iC)) (φ : L ⟶ C) [IsIso φ]
    (X : SchemeOverField k) (π : scheme k 3 ⟶ X.left) (U : X.left.Opens)
    (h : IsLineConicQuotient iL iC φ X π U),
    ¬ ProjectiveVariety X)

