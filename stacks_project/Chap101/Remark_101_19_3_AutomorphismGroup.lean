module

public import stacks_project.Chap101.Lemma_101_19_2_AutomorphismGroup
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Definition_67_40_1_Proper

/-!
# Automorphism-group properties at a point

A property `P` of algebraic spaces over fields that is invariant under ground
field extensions descends from field-valued representatives to a well-defined
property of a point `x ∈ |X|` of an algebraic stack. Finite, smooth, and
proper automorphism groups at a point are the standing examples.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Smooth morphisms of algebraic spaces are invariant under ground field
extensions. -/
instance smooth_isInvariantUnderGroundFieldExtension {S : Scheme.{u}} :
    IsInvariantUnderGroundFieldExtension (@AlgebraicSpace.Smooth S) :=
  sorry

/-- Proper morphisms of algebraic spaces are invariant under ground field
extensions. -/
instance proper_isInvariantUnderGroundFieldExtension {S : Scheme.{u}} :
    IsInvariantUnderGroundFieldExtension (@AlgebraicSpace.Proper S) :=
  sorry

namespace automorphismGroup

/-- The automorphism group of an algebraic stack at a point has a morphism
property `P` of algebraic spaces over fields, invariant under ground field
extensions, when every field-valued representative of the point has `P`. -/
def HasAt {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] (x : |X|) : Prop :=
  ∀ p : FieldValuedPoint X, Points.mk p = x → Has P p

/-- The automorphism group at a point has `P` if and only if some field-valued
representative has `P`. -/
theorem HasAt_iff_exists {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] (x : |X|) :
    HasAt P x ↔ ∃ p : FieldValuedPoint X, Points.mk p = x ∧ Has P p :=
  sorry

namespace HasAt

/-- If the automorphism group at `x` has `P`, then the automorphism group of
every field-valued representative of `x` has `P`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] {x : |X|} :
    HasAt P x → ∀ p : FieldValuedPoint X, Points.mk p = x → Has P p :=
  sorry

/-- If the automorphism group of a field-valued representative of `x` has `P`,
then the automorphism group at `x` has `P`. -/
theorem of_fieldValuedPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] {x : |X|} {p : FieldValuedPoint X} :
    Points.mk p = x → Has P p → HasAt P x :=
  sorry

end HasAt

/-- The automorphism group of an algebraic stack at a point is finite. -/
def IsFinite {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) : Prop :=
  HasAt (@AlgebraicSpace.IsFinite S) x

/-- The automorphism group at `x` is finite if and only if the structure
morphism of the automorphism group of every field-valued representative is
finite. -/
theorem IsFinite_iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) :
    IsFinite x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x →
        Has (@AlgebraicSpace.IsFinite S) p :=
  sorry

/-- The automorphism group of an algebraic stack at a point is smooth. -/
def Smooth {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) : Prop :=
  HasAt (@AlgebraicSpace.Smooth S) x

/-- The automorphism group at `x` is smooth if and only if the structure
morphism of the automorphism group of every field-valued representative is
smooth. -/
theorem Smooth_iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) :
    Smooth x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x →
        Has (@AlgebraicSpace.Smooth S) p :=
  sorry

/-- The automorphism group of an algebraic stack at a point is proper. -/
def Proper {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) : Prop :=
  HasAt (@AlgebraicSpace.Proper S) x

/-- The automorphism group at `x` is proper if and only if the structure
morphism of the automorphism group of every field-valued representative is
proper. -/
theorem Proper_iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) :
    Proper x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x →
        Has (@AlgebraicSpace.Proper S) p :=
  sorry

end automorphismGroup

end AlgebraicGeometry.AlgebraicStack
