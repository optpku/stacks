module

public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Over
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Reduction inclusions of algebraic spaces

A reduction inclusion is a closed immersion from a reduced algebraic space that
is surjective on points. Representable reductions are obtained from the
scheme-level relative reduction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebraic space over `S` represented by the scheme-theoretic reduction of a
scheme `T` over `S`. -/
def ofOverReduction {S : Scheme.{u}} (T : Over S) : AlgebraicSpace S :=
  ofOver (Over.reduction T)

/-- The closed immersion of algebraic spaces induced by the relative reduction
inclusion of a scheme over `S`. -/
def ofOverReductionι {S : Scheme.{u}} (T : Over S) :
    ofOverReduction T ⟶ ofOver T :=
  ofOverMap (Over.reductionι T)

/-- A morphism of algebraic spaces is a reduction inclusion when it is a closed
immersion from a reduced source and is surjective on points. -/
class IsReduction {S : Scheme.{u}} {Xred X : AlgebraicSpace S} (ι : Xred ⟶ X) : Prop where
  /-- A reduction inclusion is a closed immersion. -/
  closedImmersion : IsClosedImmersion ι
  /-- The source of a reduction inclusion is reduced. -/
  reduced : IsReduced Xred
  /-- A reduction inclusion is surjective on points. -/
  surjectiveOnPoints : Function.Surjective (Points.map ι)

/-- A closed immersion from a reduced algebraic space that is surjective on points
is a reduction inclusion. -/
theorem IsReduction.of {S : Scheme.{u}} {Xred X : AlgebraicSpace S} {ι : Xred ⟶ X}
    [IsClosedImmersion ι] [IsReduced Xred]
    (h : Function.Surjective (Points.map ι)) : IsReduction ι :=
  sorry

/-- A morphism of algebraic spaces is a reduction inclusion if and only if it is a
closed immersion from a reduced source and is surjective on points. -/
theorem isReduction_iff {S : Scheme.{u}} {Xred X : AlgebraicSpace S} (ι : Xred ⟶ X) :
    IsReduction ι ↔
      IsClosedImmersion ι ∧ IsReduced Xred ∧ Function.Surjective (Points.map ι) :=
  sorry

/-- A reduction inclusion is a closed immersion from a reduced algebraic space and is
surjective on points. -/
theorem IsReduction.spec {S : Scheme.{u}} {Xred X : AlgebraicSpace S} (ι : Xred ⟶ X)
    [IsReduction ι] :
    IsClosedImmersion ι ∧ IsReduced Xred ∧ Function.Surjective (Points.map ι) :=
  sorry

/-- The identity of a reduced algebraic space is a reduction inclusion. -/
instance instIsReduction_id {S : Scheme.{u}} {X : AlgebraicSpace S} [IsReduced X] :
    IsReduction (𝟙 X) :=
  sorry

/-- The relative reduction inclusion of a scheme over `S`, viewed as a morphism of
algebraic spaces, is a reduction inclusion. -/
instance instIsReduction_ofOverReductionι {S : Scheme.{u}} (T : Over S) :
    IsReduction (ofOverReductionι T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
