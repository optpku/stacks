module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.Topology.Adic.Basic
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType

/-!
# Special-fiber finite type and adic completeness

Comparison maps `A ⧸ I →+* B ⧸ I.map φ` express finite type on special fibers.
Their finite type and adic completeness give recognition predicates for
continuous homomorphisms of adic rings.
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
  rfl

/-- `mapQuotient` is compatible with the quotient maps of `φ`. -/
theorem mapQuotient_comp (φ : A →+* B) (I : Ideal A) :
    (φ.mapQuotient I).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map φ)).comp φ :=
  Ideal.quotientMap_comp_mk Ideal.le_comap_map

/-- `B`, with the algebra structure induced by `φ`, is `I`-adically complete and
has finite-type special fiber over `A ⧸ I`. -/
def IsTopologicallyFiniteTypeFor (φ : A →+* B) (I : Ideal A) : Prop :=
  @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra

/-- Adic completeness and finite type of the special fiber along `φ` are expressed
by `Algebra.TopologicallyFiniteType` for `φ.toAlgebra`. -/
theorem isTopologicallyFiniteTypeFor_iff (φ : A →+* B) (I : Ideal A) :
    φ.IsTopologicallyFiniteTypeFor I ↔
      @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra :=
  Iff.rfl

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
  Iff.rfl

namespace IsFiniteTypeOnSomeSpecialFiber

/-- Finite type of the comparison map at an ideal of definition implies finite type
on some special fiber. -/
theorem of {φ : A →+* B} {I : Ideal A} (hI : IsIdealOfDefinition I)
    (hft : (φ.mapQuotient I).FiniteType) : φ.IsFiniteTypeOnSomeSpecialFiber :=
  ⟨I, hI, hft⟩

/-- Finite type on some special fiber yields an ideal of definition and finite
type of the corresponding comparison map. -/
theorem spec {φ : A →+* B} (h : φ.IsFiniteTypeOnSomeSpecialFiber) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ (φ.mapQuotient I).FiniteType :=
  h

end IsFiniteTypeOnSomeSpecialFiber

/-- Finite type of `φ.mapQuotient I` for every ideal of definition `I` of `A`. -/
def IsFiniteTypeOnEverySpecialFiber (φ : A →+* B) : Prop :=
  ∀ I : Ideal A, IsIdealOfDefinition I → (φ.mapQuotient I).FiniteType

/-- Finite type on every special fiber means every ideal-of-definition comparison
map is of finite type. -/
theorem isFiniteTypeOnEverySpecialFiber_iff (φ : A →+* B) :
    φ.IsFiniteTypeOnEverySpecialFiber ↔
      ∀ I : Ideal A, IsIdealOfDefinition I → (φ.mapQuotient I).FiniteType :=
  Iff.rfl

namespace IsFiniteTypeOnEverySpecialFiber

/-- Finite type of the comparison maps at all ideals of definition implies finite
type on every special fiber. -/
theorem of {φ : A →+* B}
    (h : ∀ I : Ideal A, IsIdealOfDefinition I → (φ.mapQuotient I).FiniteType) :
    φ.IsFiniteTypeOnEverySpecialFiber :=
  h

/-- Finite type on every special fiber yields finite type of each comparison map. -/
theorem spec {φ : A →+* B} (h : φ.IsFiniteTypeOnEverySpecialFiber) {I : Ideal A}
    (hI : IsIdealOfDefinition I) : (φ.mapQuotient I).FiniteType :=
  h I hI

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
  Iff.rfl

namespace IsAdicAndFiniteTypeOnEverySpecialFiber

/-- Adic topology and finite type of the comparison map at every ideal of
definition imply the universal adic special-fiber condition. -/
theorem of {φ : A →+* B}
    (h : ∀ I : Ideal A, IsIdealOfDefinition I →
      IsAdic (I.map φ) ∧ (φ.mapQuotient I).FiniteType) :
    φ.IsAdicAndFiniteTypeOnEverySpecialFiber :=
  h

/-- The paired condition at every ideal of definition yields the `I`-adic topology
and finite type of the comparison map. -/
theorem spec {φ : A →+* B} (h : φ.IsAdicAndFiniteTypeOnEverySpecialFiber)
    {I : Ideal A} (hI : IsIdealOfDefinition I) :
    IsAdic (I.map φ) ∧ (φ.mapQuotient I).FiniteType :=
  h I hI

end IsAdicAndFiniteTypeOnEverySpecialFiber

/-- There is an ideal of definition `I` such that the topology on `B` is the
`I`-adic topology and `B` is an `I`-adically complete algebra with finite-type
special fiber along `φ`. -/
def IsAdicAndTopologicallyFiniteTypeOnSome (φ : A →+* B) : Prop :=
  ∃ I : Ideal A, IsIdealOfDefinition I ∧ IsAdic (I.map φ) ∧
    φ.IsTopologicallyFiniteTypeFor I

/-- The existential adic complete finite-type condition holds exactly when an
ideal of definition induces the target topology and a complete finite-type algebra. -/
theorem isAdicAndTopologicallyFiniteTypeOnSome_iff (φ : A →+* B) :
    φ.IsAdicAndTopologicallyFiniteTypeOnSome ↔
      ∃ I : Ideal A, IsIdealOfDefinition I ∧ IsAdic (I.map φ) ∧
        φ.IsTopologicallyFiniteTypeFor I :=
  Iff.rfl

namespace IsAdicAndTopologicallyFiniteTypeOnSome

/-- An ideal of definition inducing the target topology and a complete finite-type
algebra satisfies the existential adic complete finite-type condition. -/
theorem of {φ : A →+* B} {I : Ideal A} (hI : IsIdealOfDefinition I)
    (hadic : IsAdic (I.map φ)) (hC : φ.IsTopologicallyFiniteTypeFor I) :
    φ.IsAdicAndTopologicallyFiniteTypeOnSome :=
  ⟨I, hI, hadic, hC⟩

/-- The existential adic complete finite-type condition yields an ideal of
definition inducing the target topology and a complete finite-type algebra. -/
theorem spec {φ : A →+* B} (h : φ.IsAdicAndTopologicallyFiniteTypeOnSome) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ IsAdic (I.map φ) ∧
      φ.IsTopologicallyFiniteTypeFor I :=
  h

end IsAdicAndTopologicallyFiniteTypeOnSome

/-- For every ideal of definition `I`, the topology on `B` is the `I`-adic topology
and `B` is an `I`-adically complete algebra with finite-type special fiber
along `φ`. -/
def IsAdicAndTopologicallyFiniteTypeOnEvery (φ : A →+* B) : Prop :=
  ∀ I : Ideal A, IsIdealOfDefinition I →
    IsAdic (I.map φ) ∧ φ.IsTopologicallyFiniteTypeFor I

/-- The universal adic complete finite-type condition holds exactly when every
ideal of definition induces the target topology and a complete finite-type algebra. -/
theorem isAdicAndTopologicallyFiniteTypeOnEvery_iff (φ : A →+* B) :
    φ.IsAdicAndTopologicallyFiniteTypeOnEvery ↔
      ∀ I : Ideal A, IsIdealOfDefinition I →
        IsAdic (I.map φ) ∧ φ.IsTopologicallyFiniteTypeFor I :=
  Iff.rfl

namespace IsAdicAndTopologicallyFiniteTypeOnEvery

/-- Adic topology and a complete finite-type algebra at every ideal of definition
satisfy the universal adic complete finite-type condition. -/
theorem of {φ : A →+* B}
    (h : ∀ I : Ideal A, IsIdealOfDefinition I →
      IsAdic (I.map φ) ∧ φ.IsTopologicallyFiniteTypeFor I) :
    φ.IsAdicAndTopologicallyFiniteTypeOnEvery :=
  h

/-- The universal adic complete finite-type condition gives the adic topology
and a complete finite-type algebra at each ideal of definition. -/
theorem spec {φ : A →+* B} (h : φ.IsAdicAndTopologicallyFiniteTypeOnEvery)
    {I : Ideal A} (hI : IsIdealOfDefinition I) :
    IsAdic (I.map φ) ∧ φ.IsTopologicallyFiniteTypeFor I :=
  h I hI

end IsAdicAndTopologicallyFiniteTypeOnEvery

end SpecialFiber

end RingHom
