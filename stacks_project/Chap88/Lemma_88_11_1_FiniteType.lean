/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.Topology.Adic.Basic
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»

/-!
# Special-fiber finite type and category (88.2.0.2)

Comparison maps `A ⧸ I →+* B ⧸ I B` and the special-fiber / (88.2.0.2)
conditions used to recognize adic topologically finite type arrows.
-/

@[expose] public section

universe u

open TopologicalRing
open TopologicalRing.Ideal

namespace RingHom

section MapQuotient

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The comparison homomorphism `A ⧸ I →+* B ⧸ I.map φ` induced by `φ`. -/
def mapQuotient (φ : A →+* B) (I : Ideal A) : A ⧸ I →+* B ⧸ I.map φ :=
  Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map

/-- `mapQuotient` is `Ideal.quotientMap` along `Ideal.le_comap_map`. -/
theorem mapQuotient_def (φ : A →+* B) (I : Ideal A) :
    φ.mapQuotient I = Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map :=
  sorry

/-- `mapQuotient` is compatible with the quotient maps of `φ`. -/
theorem mapQuotient_comp (φ : A →+* B) (I : Ideal A) :
    (φ.mapQuotient I).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map φ)).comp φ :=
  sorry

/-- `B` lies in the category (88.2.0.2) relative to `I` along `φ`. -/
def IsTopologicallyFiniteTypeFor (φ : A →+* B) (I : Ideal A) : Prop :=
  @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra

/-- Membership in (88.2.0.2) along `φ` is `Algebra.TopologicallyFiniteType` via `φ.toAlgebra`. -/
theorem isTopologicallyFiniteTypeFor_iff (φ : A →+* B) (I : Ideal A) :
    φ.IsTopologicallyFiniteTypeFor I ↔
      @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra :=
  sorry

end MapQuotient

section SpecialFiber

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A]
variable [CommRing B] [TopologicalSpace B]

/-- Finite type of `φ.mapQuotient I` for some ideal of definition `I` of `A`. -/
def IsFiniteTypeOnSomeSpecialFiber (φ : A →+* B) : Prop :=
  ∃ I : Ideal A, IsIdealOfDefinition I ∧ (φ.mapQuotient I).FiniteType

/-- Finite type on some special fiber is existence of an ideal of definition with
finite-type comparison map. -/
theorem isFiniteTypeOnSomeSpecialFiber_iff (φ : A →+* B) :
    φ.IsFiniteTypeOnSomeSpecialFiber ↔
      ∃ I : Ideal A, IsIdealOfDefinition I ∧ (φ.mapQuotient I).FiniteType :=
  sorry

namespace IsFiniteTypeOnSomeSpecialFiber

/-- Package finite type of `φ.mapQuotient I` at an ideal of definition. -/
theorem of {φ : A →+* B} {I : Ideal A} (hI : IsIdealOfDefinition I)
    (hft : (φ.mapQuotient I).FiniteType) : φ.IsFiniteTypeOnSomeSpecialFiber :=
  sorry

/-- Finite type on some special fiber yields an ideal of definition and finite
type of the corresponding comparison map. -/
theorem spec {φ : A →+* B} (h : φ.IsFiniteTypeOnSomeSpecialFiber) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ (φ.mapQuotient I).FiniteType :=
  sorry

end IsFiniteTypeOnSomeSpecialFiber

/-- Finite type of `φ.mapQuotient I` for every ideal of definition `I` of `A`. -/
def IsFiniteTypeOnEverySpecialFiber (φ : A →+* B) : Prop :=
  ∀ I : Ideal A, IsIdealOfDefinition I → (φ.mapQuotient I).FiniteType

/-- Finite type on every special fiber means every ideal-of-definition comparison
map is of finite type. -/
theorem isFiniteTypeOnEverySpecialFiber_iff (φ : A →+* B) :
    φ.IsFiniteTypeOnEverySpecialFiber ↔
      ∀ I : Ideal A, IsIdealOfDefinition I → (φ.mapQuotient I).FiniteType :=
  sorry

namespace IsFiniteTypeOnEverySpecialFiber

/-- Package pointwise finite type of special-fiber comparison maps. -/
theorem of {φ : A →+* B}
    (h : ∀ I : Ideal A, IsIdealOfDefinition I → (φ.mapQuotient I).FiniteType) :
    φ.IsFiniteTypeOnEverySpecialFiber :=
  sorry

/-- Finite type on every special fiber yields finite type of each comparison map. -/
theorem spec {φ : A →+* B} (h : φ.IsFiniteTypeOnEverySpecialFiber) {I : Ideal A}
    (hI : IsIdealOfDefinition I) : (φ.mapQuotient I).FiniteType :=
  sorry

end IsFiniteTypeOnEverySpecialFiber

/-- For every ideal of definition `I`, the topology on `B` is the `I`-adic topology
and `A ⧸ I →+* B ⧸ I B` is of finite type. -/
def IsAdicAndFiniteTypeOnEverySpecialFiber (φ : A →+* B) : Prop :=
  ∀ I : Ideal A, IsIdealOfDefinition I →
    IsAdic (I.map φ) ∧ (φ.mapQuotient I).FiniteType

/-- The paired “every ideal of definition” form unpacks as `I`-adic topology together
with finite type of `φ.mapQuotient I`. -/
theorem isAdicAndFiniteTypeOnEverySpecialFiber_iff (φ : A →+* B) :
    φ.IsAdicAndFiniteTypeOnEverySpecialFiber ↔
      ∀ I : Ideal A, IsIdealOfDefinition I →
        IsAdic (I.map φ) ∧ (φ.mapQuotient I).FiniteType :=
  sorry

namespace IsAdicAndFiniteTypeOnEverySpecialFiber

/-- Package the paired `I`-adic and special-fiber finite type conditions. -/
theorem of {φ : A →+* B}
    (h : ∀ I : Ideal A, IsIdealOfDefinition I →
      IsAdic (I.map φ) ∧ (φ.mapQuotient I).FiniteType) :
    φ.IsAdicAndFiniteTypeOnEverySpecialFiber :=
  sorry

/-- The paired condition at every ideal of definition yields the `I`-adic topology
and finite type of the comparison map. -/
theorem spec {φ : A →+* B} (h : φ.IsAdicAndFiniteTypeOnEverySpecialFiber)
    {I : Ideal A} (hI : IsIdealOfDefinition I) :
    IsAdic (I.map φ) ∧ (φ.mapQuotient I).FiniteType :=
  sorry

end IsAdicAndFiniteTypeOnEverySpecialFiber

/-- There is an ideal of definition `I` such that the topology on `B` is the
`I`-adic topology and `B` lies in the category (88.2.0.2) along `φ`. -/
def IsAdicAndTopologicallyFiniteTypeOnSome (φ : A →+* B) : Prop :=
  ∃ I : Ideal A, IsIdealOfDefinition I ∧ IsAdic (I.map φ) ∧
    φ.IsTopologicallyFiniteTypeFor I

/-- The “some ideal of definition” form of (88.2.0.2) unpacks as an ideal of
definition inducing the `I`-adic topology with `B` in (88.2.0.2). -/
theorem isAdicAndTopologicallyFiniteTypeOnSome_iff (φ : A →+* B) :
    φ.IsAdicAndTopologicallyFiniteTypeOnSome ↔
      ∃ I : Ideal A, IsIdealOfDefinition I ∧ IsAdic (I.map φ) ∧
        φ.IsTopologicallyFiniteTypeFor I :=
  sorry

namespace IsAdicAndTopologicallyFiniteTypeOnSome

/-- Package an ideal of definition inducing the `I`-adic topology with membership
in (88.2.0.2). -/
theorem of {φ : A →+* B} {I : Ideal A} (hI : IsIdealOfDefinition I)
    (hadic : IsAdic (I.map φ)) (hC : φ.IsTopologicallyFiniteTypeFor I) :
    φ.IsAdicAndTopologicallyFiniteTypeOnSome :=
  sorry

/-- The “some ideal of definition” form yields an ideal of definition, the `I`-adic
topology, and membership in (88.2.0.2). -/
theorem spec {φ : A →+* B} (h : φ.IsAdicAndTopologicallyFiniteTypeOnSome) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ IsAdic (I.map φ) ∧
      φ.IsTopologicallyFiniteTypeFor I :=
  sorry

end IsAdicAndTopologicallyFiniteTypeOnSome

/-- For every ideal of definition `I`, the topology on `B` is the `I`-adic topology
and `B` lies in the category (88.2.0.2) along `φ`. -/
def IsAdicAndTopologicallyFiniteTypeOnEvery (φ : A →+* B) : Prop :=
  ∀ I : Ideal A, IsIdealOfDefinition I →
    IsAdic (I.map φ) ∧ φ.IsTopologicallyFiniteTypeFor I

/-- The “every ideal of definition” form of (88.2.0.2) unpacks as `I`-adic topology
together with membership in (88.2.0.2). -/
theorem isAdicAndTopologicallyFiniteTypeOnEvery_iff (φ : A →+* B) :
    φ.IsAdicAndTopologicallyFiniteTypeOnEvery ↔
      ∀ I : Ideal A, IsIdealOfDefinition I →
        IsAdic (I.map φ) ∧ φ.IsTopologicallyFiniteTypeFor I :=
  sorry

namespace IsAdicAndTopologicallyFiniteTypeOnEvery

/-- Package the paired `I`-adic and (88.2.0.2) conditions at every ideal of
definition. -/
theorem of {φ : A →+* B}
    (h : ∀ I : Ideal A, IsIdealOfDefinition I →
      IsAdic (I.map φ) ∧ φ.IsTopologicallyFiniteTypeFor I) :
    φ.IsAdicAndTopologicallyFiniteTypeOnEvery :=
  sorry

/-- The paired condition at every ideal of definition yields the `I`-adic topology
and membership in (88.2.0.2). -/
theorem spec {φ : A →+* B} (h : φ.IsAdicAndTopologicallyFiniteTypeOnEvery)
    {I : Ideal A} (hI : IsIdealOfDefinition I) :
    IsAdic (I.map φ) ∧ φ.IsTopologicallyFiniteTypeFor I :=
  sorry

end IsAdicAndTopologicallyFiniteTypeOnEvery

end SpecialFiber

end RingHom
