module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap69.Lemma_69_19_1_DVR
public import stacks_project.Chap69.Lemma_69_19_2_DVR

/-!
# Complete DVR valuative criterion for morphisms of algebraic spaces

A morphism of algebraic spaces satisfies the uniqueness part of the complete
DVR valuative criterion when every valuative square whose ring is a complete
discrete valuation ring has at most one lift, and the existence part when every
such square admits a complete discrete valuation ring extension together with a
unique lift of the extended square.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces satisfies the uniqueness part of the complete
DVR valuative criterion if every valuative commutative square whose ring is a
complete discrete valuation ring has at most one lift. -/
@[mk_iff]
class ValuativeCriterion.CompleteDVR.Uniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every complete DVR valuative square has at most one dotted lift. -/
  subsingleton_liftStruct :
    ∀ sq : ValuativeCommSq f,
      IsDiscreteValuationRing sq.R → IsCompleteLocalRing sq.R →
        Subsingleton sq.commSq.LiftStruct

namespace ValuativeCriterion.CompleteDVR.Uniqueness

/-- The identity morphism of an algebraic space satisfies complete DVR uniqueness. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Uniqueness (𝟙 X) := sorry

/-- Uniqueness for all discrete valuation rings implies uniqueness for complete
discrete valuation rings. -/
instance of_dvrUniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Uniqueness f] : Uniqueness f := sorry

/-- A morphism satisfies complete DVR uniqueness if and only if every complete
DVR valuative square has at most one lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Uniqueness f ↔
      ∀ sq : ValuativeCommSq f,
        IsDiscreteValuationRing sq.R → IsCompleteLocalRing sq.R →
          Subsingleton sq.commSq.LiftStruct :=
  sorry

end ValuativeCriterion.CompleteDVR.Uniqueness

/-- A morphism of algebraic spaces satisfies the existence part of the complete
DVR valuative criterion if every valuative commutative square whose ring is a
complete discrete valuation ring admits an extension `A ⊂ A'` of complete
discrete valuation rings together with a unique lift `Spec(A') ⟶ X`. -/
@[mk_iff]
class ValuativeCriterion.CompleteDVR.Existence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every complete DVR valuative square admits a complete DVR extension with a
  unique lift `Spec(A') ⟶ X` of the extended square. -/
  nonempty_extension :
    ∀ sq : ValuativeCommSq f,
      IsDiscreteValuationRing sq.R → IsCompleteLocalRing sq.R →
        ∃ e : sq.Extension,
          IsDiscreteValuationRing e.R' ∧ IsCompleteLocalRing e.R' ∧
            Subsingleton e.outerCommSq.LiftStruct

namespace ValuativeCriterion.CompleteDVR.Existence

/-- The identity morphism of an algebraic space satisfies complete DVR existence. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Existence (𝟙 X) := sorry

/-- A morphism satisfies complete DVR existence if and only if every complete
DVR valuative square admits a complete DVR extension with a unique lift
`Spec(A') ⟶ X`. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Existence f ↔
      ∀ sq : ValuativeCommSq f,
        IsDiscreteValuationRing sq.R → IsCompleteLocalRing sq.R →
          ∃ e : sq.Extension,
            IsDiscreteValuationRing e.R' ∧ IsCompleteLocalRing e.R' ∧
              Subsingleton e.outerCommSq.LiftStruct :=
  sorry

end ValuativeCriterion.CompleteDVR.Existence

/-- A morphism of algebraic spaces satisfies the complete DVR valuative criterion
if it satisfies both the uniqueness and existence parts. -/
@[mk_iff]
class ValuativeCriterion.CompleteDVR {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop
    extends ValuativeCriterion.CompleteDVR.Uniqueness f,
      ValuativeCriterion.CompleteDVR.Existence f

namespace ValuativeCriterion.CompleteDVR

/-- The identity morphism of an algebraic space satisfies the complete DVR
valuative criterion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    ValuativeCriterion.CompleteDVR (𝟙 X) :=
  sorry

/-- A morphism satisfies the complete DVR valuative criterion if and only if it
satisfies both the uniqueness and existence parts. -/
theorem iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ValuativeCriterion.CompleteDVR f ↔ Uniqueness f ∧ Existence f :=
  sorry

end ValuativeCriterion.CompleteDVR

/-- A class of discrete valuation rings is extension-dense if every discrete
valuation ring admits an extension belonging to the class. -/
@[mk_iff]
class ValuativeCriterion.DVR.ExtensionDense
    (P : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], Prop) :
    Prop where
  /-- Every discrete valuation ring admits an extension in the class `P`. -/
  exists_extension :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
      ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
        (_ : Algebra R R'),
        IsExtensionOfDiscreteValuationRings R R' ∧ P R'

namespace ValuativeCriterion.DVR.ExtensionDense

/-- Complete discrete valuation rings form an extension-dense class: every
discrete valuation ring admits a complete discrete valuation ring extension. -/
instance completeLocalRing :
    ExtensionDense fun (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] ↦
      IsCompleteLocalRing R :=
  sorry

/-- A predicate on discrete valuation rings is extension-dense if and only if
every discrete valuation ring admits an extension in the class. -/
theorem spec
    (P : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], Prop) :
    ExtensionDense P ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
        ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
          (_ : Algebra R R'),
          IsExtensionOfDiscreteValuationRings R R' ∧ P R' :=
  sorry

end ValuativeCriterion.DVR.ExtensionDense

namespace ValuativeCriterion.DVR.Uniqueness

/-- Complete DVR uniqueness implies uniqueness for all discrete valuation rings. -/
theorem of_completeDVR {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.CompleteDVR.Uniqueness f] : Uniqueness f :=
  sorry

end ValuativeCriterion.DVR.Uniqueness

namespace ValuativeCriterion.DVR.Existence

/-- After a separated morphism, complete DVR existence implies existence of a
lift on every DVR valuative square. -/
theorem of_completeDVR {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [ValuativeCriterion.CompleteDVR.Existence f] : Existence f :=
  sorry

end ValuativeCriterion.DVR.Existence

end AlgebraicGeometry.AlgebraicSpace
