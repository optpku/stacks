module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Topology.Algebra.LinearTopology
public import stacks_project.Chap87.«87_21_2_1_Completion»

/-!
# Localization squares for countably indexed weakly admissible rings

A localization square is a commutative diagram
`A ⟶ (A')^∧`, `B ⟶ (B')^∧` with vertical maps `φ : B ⟶ A` and
`φ' : (B')^∧ ⟶ (A')^∧`, where `A, B` are countably indexed weakly admissible
rings, `A → A'` and `B → B'` are étale ring maps, the completions are weak-ideal
inverse limits, and `φ`, `φ'` are continuous. This is Stacks, Tag 0ANC.
-/

@[expose] public section

universe u

open CategoryTheory Filter Topology

namespace TopologicalRing

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- A topological ring is countably indexed when it has a countable fundamental system of
open ideals. -/
class IsCountablyIndexed (R : Type u) [CommRing R] [TopologicalSpace R] : Prop where
  /-- There is a countable family of open ideals forming a neighborhood basis at `0`. -/
  exists_countable_open_ideal_basis :
    ∃ I : ℕ → Ideal R,
      (∀ n, IsOpen (I n : Set R)) ∧
        (nhds (0 : R)).HasBasis (fun _ : ℕ => True) (fun n => (I n : Set R))

/-- A countable family of open ideals forming a neighborhood basis at `0` makes the ring
countably indexed. -/
theorem IsCountablyIndexed.of_hasBasis {I : ℕ → Ideal R} (hI : ∀ n, IsOpen (I n : Set R))
    (hbasis : (nhds (0 : R)).HasBasis (fun _ : ℕ => True) (fun n => (I n : Set R))) :
    IsCountablyIndexed R := sorry

/-- Under a linear topology, countable indexing is equivalent to countably generated
neighborhoods of `0`. -/
theorem isCountablyIndexed_iff_nhds_isCountablyGenerated
    [IsTopologicalRing R] [IsLinearTopology R R] :
    IsCountablyIndexed R ↔ (nhds (0 : R)).IsCountablyGenerated := sorry

/-- A linearly topologized ring with countably generated neighborhoods of `0` is countably
indexed. -/
instance instIsCountablyIndexed [IsTopologicalRing R] [IsLinearTopology R R]
    [(nhds (0 : R)).IsCountablyGenerated] : IsCountablyIndexed R := sorry

/-- A localization square is a commutative diagram `A ⟶ (A')^∧`, `B ⟶ (B')^∧` with
continuous vertical maps `φ : B ⟶ A` and `φ' : (B')^∧ ⟶ (A')^∧`. -/
structure LocalizeSquare (A B A' B' : Type u)
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    [CommRing B'] [Algebra B B'] [Algebra.Etale B B'] where
  /-- The continuous ring map `φ : B ⟶ A`. -/
  φ : B →+* A
  /-- Continuity of `φ`. -/
  continuous_φ : Continuous φ
  /-- The continuous ring map `φ' : (B')^∧ ⟶ (A')^∧`. -/
  φ' : weakIdealCompletion B B' →+* weakIdealCompletion A A'
  /-- Continuity of `φ'`. -/
  continuous_φ' : Continuous φ'
  /-- The square commutes: `φ'` after `B ⟶ (B')^∧` equals `A ⟶ (A')^∧` after `φ`. -/
  w : φ'.comp (algebraMap B (weakIdealCompletion B B')) =
      (algebraMap A (weakIdealCompletion A A')).comp φ

namespace LocalizeSquare

variable {A B A' B' : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
variable [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
variable [CommRing B'] [Algebra B B'] [Algebra.Etale B B']

/-- Package a localization square from its primitive maps, continuity, and commutativity. -/
def of (φ : B →+* A) (continuous_φ : Continuous φ)
    (φ' : weakIdealCompletion B B' →+* weakIdealCompletion A A')
    (continuous_φ' : Continuous φ')
    (w : φ'.comp (algebraMap B (weakIdealCompletion B B')) =
      (algebraMap A (weakIdealCompletion A A')).comp φ) :
    LocalizeSquare A B A' B' where
  φ := φ
  continuous_φ := continuous_φ
  φ' := φ'
  continuous_φ' := continuous_φ'
  w := w

/-- Package a localization square from étale ring maps `A → A'` and `B → B'`. -/
def ofRingHom (_ : (algebraMap A A').Etale) (_ : (algebraMap B B').Etale)
    (φ : B →+* A) (continuous_φ : Continuous φ)
    (φ' : weakIdealCompletion B B' →+* weakIdealCompletion A A')
    (continuous_φ' : Continuous φ')
    (w : φ'.comp (algebraMap B (weakIdealCompletion B B')) =
      (algebraMap A (weakIdealCompletion A A')).comp φ) :
    LocalizeSquare A B A' B' :=
  of φ continuous_φ φ' continuous_φ' w

/-- The underlying commutative square in `CommRingCat`. -/
theorem commSq (sq : LocalizeSquare A B A' B') :
    CommSq
      (CommRingCat.ofHom (algebraMap B (weakIdealCompletion B B')))
      (CommRingCat.ofHom sq.φ)
      (CommRingCat.ofHom sq.φ')
      (CommRingCat.ofHom (algebraMap A (weakIdealCompletion A A'))) := sorry

/-- Pointwise form of commutativity of a localization square. -/
theorem w_apply (sq : LocalizeSquare A B A' B') (b : B) :
    sq.φ' (algebraMap B (weakIdealCompletion B B') b) =
      algebraMap A (weakIdealCompletion A A') (sq.φ b) := sorry

/-- The ring map `A → A'` in a localization square is étale. -/
theorem algebraMap_etale (sq : LocalizeSquare A B A' B') :
    (algebraMap A A').Etale := sorry

/-- The ring map `B → B'` in a localization square is étale. -/
theorem algebraMap_etale_source (sq : LocalizeSquare A B A' B') :
    (algebraMap B B').Etale := sorry

end LocalizeSquare

end TopologicalRing
