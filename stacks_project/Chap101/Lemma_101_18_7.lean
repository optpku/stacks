/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap101.Lemma_101_18_4_FiniteTypePoint
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap100.Definition_100_11_8_ResidualGerbe

/-!
# Characterizations of finite-type points of algebraic stacks

A point of an algebraic stack is of finite type if and only if it is the image
of a locally-of-finite-type morphism from a singleton algebraic stack, and if
and only if the residual gerbe at that point exists with
locally-of-finite-type inclusion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (x : Points X)

/-- There exists an algebraic stack `Z` over `S` whose space of points is a
singleton, together with a locally-of-finite-type morphism `f : Z ⟶ X` whose
image on points is `{x}`. -/
def existsSingletonLocallyOfFiniteType : Prop :=
  ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
    Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧ LocallyOfFiniteType f ∧
      Set.range (Points.map f) = {x}

/-- `existsSingletonLocallyOfFiniteType x` means some locally-of-finite-type
morphism from a singleton algebraic stack has image `{x}` on points. -/
theorem existsSingletonLocallyOfFiniteType_iff :
    existsSingletonLocallyOfFiniteType x ↔
      ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
        Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧ LocallyOfFiniteType f ∧
          Set.range (Points.map f) = {x} :=
  sorry

/-- `existsSingletonLocallyOfFiniteType x` is equivalent to the existence of a
locally-of-finite-type morphism from an algebraic stack whose underlying point
set is a singleton `{z}` with image `{x}`. -/
theorem existsSingletonLocallyOfFiniteType_iff_univ :
    existsSingletonLocallyOfFiniteType x ↔
      ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X) (z : Points Z),
        (Set.univ : Set (Points Z)) = {z} ∧ LocallyOfFiniteType f ∧
          Set.range (Points.map f) = {x} :=
  sorry

namespace existsSingletonLocallyOfFiniteType

/-- A locally-of-finite-type morphism from a singleton algebraic stack with
image `{x}` witnesses `existsSingletonLocallyOfFiniteType x`. -/
theorem of {Z : GroupoidsOver S} [AlgebraicStack Z] {f : Z ⟶ X}
    [Nonempty (Points Z)] [Subsingleton (Points Z)] [LocallyOfFiniteType f]
    (hx : Set.range (Points.map f) = {x}) :
    existsSingletonLocallyOfFiniteType x :=
  sorry

/-- `existsSingletonLocallyOfFiniteType x` supplies a singleton algebraic stack
over `S` and a locally-of-finite-type morphism to `X` with image `{x}`. -/
theorem spec (h : existsSingletonLocallyOfFiniteType x) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
      Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧ LocallyOfFiniteType f ∧
        Set.range (Points.map f) = {x} :=
  sorry

end existsSingletonLocallyOfFiniteType

/-- The residual gerbe of `X` at `x` exists and its inclusion
`residualGerbeι X x` is locally of finite type. -/
def existsResidualGerbeLocallyOfFiniteType : Prop :=
  ∃ _ : HasResidualGerbe X x, LocallyOfFiniteType (residualGerbeι X x)

/-- `existsResidualGerbeLocallyOfFiniteType x` means the residual gerbe of `X`
at `x` exists and `residualGerbeι X x` is locally of finite type. -/
theorem existsResidualGerbeLocallyOfFiniteType_iff :
    existsResidualGerbeLocallyOfFiniteType x ↔
      ∃ _ : HasResidualGerbe X x, LocallyOfFiniteType (residualGerbeι X x) :=
  sorry

namespace existsResidualGerbeLocallyOfFiniteType

/-- If the residual gerbe of `X` at `x` exists and its inclusion is locally of
finite type, then `existsResidualGerbeLocallyOfFiniteType x` holds. -/
theorem of [HasResidualGerbe X x] [LocallyOfFiniteType (residualGerbeι X x)] :
    existsResidualGerbeLocallyOfFiniteType x :=
  sorry

/-- `existsResidualGerbeLocallyOfFiniteType x` supplies existence of the
residual gerbe of `X` at `x` together with local finite type of
`residualGerbeι X x`. -/
theorem spec (h : existsResidualGerbeLocallyOfFiniteType x) :
    ∃ _ : HasResidualGerbe X x, LocallyOfFiniteType (residualGerbeι X x) :=
  sorry

end existsResidualGerbeLocallyOfFiniteType

/-- Lemma 101.18.7: Let `X` be an algebraic stack. Let `x : Points X`. The
following are equivalent: `x` is a finite type point; there exists an algebraic
stack `Z` whose space of points is a singleton and a morphism `f : Z ⟶ X`
which is locally of finite type such that `Set.range (Points.map f) = {x}`; and
the residual gerbe of `X` at `x` exists and the inclusion
`residualGerbeι X x` is locally of finite type. -/
@[stacks 06G3]
theorem isFiniteTypePoint_tfae :
    List.TFAE
      [IsFiniteTypePoint x, existsSingletonLocallyOfFiniteType x,
        existsResidualGerbeLocallyOfFiniteType x] :=
  sorry

/-- A point of an algebraic stack is of finite type if and only if it is the
image of a locally-of-finite-type morphism from a singleton algebraic stack. -/
theorem isFiniteTypePoint_iff_existsSingletonLocallyOfFiniteType :
    IsFiniteTypePoint x ↔ existsSingletonLocallyOfFiniteType x :=
  sorry

/-- A point of an algebraic stack is of finite type if and only if the residual
gerbe at that point exists and its inclusion is locally of finite type. -/
theorem isFiniteTypePoint_iff_existsResidualGerbeLocallyOfFiniteType :
    IsFiniteTypePoint x ↔ existsResidualGerbeLocallyOfFiniteType x :=
  sorry

/-- A finite-type point of an algebraic stack has a residual gerbe. -/
theorem HasResidualGerbe.of_isFiniteTypePoint (hx : IsFiniteTypePoint x) :
    HasResidualGerbe X x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
