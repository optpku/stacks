/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.Etale.Basic
public import ReasLib.RingTheory.Topology.CountablyIndexed
public import ReasLib.RingTheory.Topology.WeakIdealCompletion

/-!
# Localization squares for countably indexed weakly admissible rings

A localization square has horizontal maps from `A` and `B` to the weak-ideal completions
of étale algebras `A'` and `B'`, respectively, and continuous vertical ring homomorphisms
making the diagram commute.
-/

@[expose] public section

universe u

open CategoryTheory Filter Topology

namespace TopologicalRing

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

/-- Construct a localization square from continuous vertical maps whose composites
with the canonical completion maps agree. -/
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

/-- The vertical maps of a localization square are continuous and commute with the
canonical maps into the weak-ideal completions. -/
theorem spec (sq : LocalizeSquare A B A' B') :
    Continuous sq.φ ∧ Continuous sq.φ' ∧
      sq.φ'.comp (algebraMap B (weakIdealCompletion B B')) =
        (algebraMap A (weakIdealCompletion A A')).comp sq.φ := sorry

end LocalizeSquare

end TopologicalRing
