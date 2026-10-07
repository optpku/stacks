module

public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Finite-type points of algebraic spaces, first characterization

A point of an algebraic space is represented by a locally-of-finite-type
morphism from the spectrum of a field if and only if it is the image of a
closed point under an étale morphism from a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X)

/-- There exists a field-valued point representing `x` whose morphism into `X` is
locally of finite type. -/
def existsLocallyOfFiniteTypeFieldValuedPoint : Prop :=
  ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x

/-- `existsLocallyOfFiniteTypeFieldValuedPoint x` means some morphism
`Spec(k) ⟶ X` is locally of finite type and represents `x`. -/
theorem existsLocallyOfFiniteTypeFieldValuedPoint_iff :
    existsLocallyOfFiniteTypeFieldValuedPoint x ↔
      ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x :=
  sorry

namespace existsLocallyOfFiniteTypeFieldValuedPoint

/-- A field-valued point of `X` whose morphism is locally of finite type and
whose class is `x` witnesses `existsLocallyOfFiniteTypeFieldValuedPoint x`. -/
theorem of {p : FieldValuedPoint X} [LocallyOfFiniteType p.hom]
    (hx : Points.mk p = x) : existsLocallyOfFiniteTypeFieldValuedPoint x :=
  sorry

/-- `existsLocallyOfFiniteTypeFieldValuedPoint x` supplies a field-valued point
representing `x` whose morphism into `X` is locally of finite type. -/
theorem spec (h : existsLocallyOfFiniteTypeFieldValuedPoint x) :
    ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x :=
  sorry

end existsLocallyOfFiniteTypeFieldValuedPoint

/-- There exists a scheme `U` over `S`, a closed point of `U`, and an étale
morphism from `ofOver U` to `X` sending that point to `x`. -/
def existsEtaleClosedPoint : Prop :=
  ∃ (U : Over S) (u : U.left) (φ : ofOver U ⟶ X),
    u ∈ closedPoints U.left ∧ Etale φ ∧ Points.mapOfOver φ u = x

/-- `existsEtaleClosedPoint x` means some étale morphism `φ : ofOver U ⟶ X`
from a scheme over `S` sends a closed point of `U` to `x`. -/
theorem existsEtaleClosedPoint_iff :
    existsEtaleClosedPoint x ↔
      ∃ (U : Over S) (u : U.left) (φ : ofOver U ⟶ X),
        u ∈ closedPoints U.left ∧ Etale φ ∧ Points.mapOfOver φ u = x :=
  sorry

namespace existsEtaleClosedPoint

/-- An étale morphism from a scheme over `S` sending a closed point to `x`
witnesses `existsEtaleClosedPoint x`. -/
theorem of {U : Over S} {u : U.left} {φ : ofOver U ⟶ X}
    (hu : u ∈ closedPoints U.left) [Etale φ] (hx : Points.mapOfOver φ u = x) :
    existsEtaleClosedPoint x :=
  sorry

/-- `existsEtaleClosedPoint x` supplies a scheme over `S`, a closed point of that
scheme, and an étale morphism to `X` sending the closed point to `x`. -/
theorem spec (h : existsEtaleClosedPoint x) :
    ∃ (U : Over S) (u : U.left) (φ : ofOver U ⟶ X),
      u ∈ closedPoints U.left ∧ Etale φ ∧ Points.mapOfOver φ u = x :=
  sorry

end existsEtaleClosedPoint

/-- Lemma 67.25.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x : Points X`. The following are equivalent: there exists a morphism
`Spec(k) ⟶ X` which is locally of finite type and represents `x`; and there
exists a scheme `U`, a closed point `u ∈ U`, and an étale morphism
`φ : U ⟶ X` such that `φ(u) = x`. -/
@[stacks 06EF]
theorem existsLocallyOfFiniteTypeFieldValuedPoint_iff_existsEtaleClosedPoint :
    existsLocallyOfFiniteTypeFieldValuedPoint x ↔ existsEtaleClosedPoint x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
