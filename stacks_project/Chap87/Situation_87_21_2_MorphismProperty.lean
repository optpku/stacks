module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import stacks_project.Chap87.Lemma_87_19_13_Completion
public import stacks_project.Chap87.Lemma_87_21_1
public import stacks_project.Chap87.«87_21_2_1_LocalizeSquare»

/-!
# Local properties of morphisms of countably indexed weakly admissible rings

A property of morphisms of countably indexed weakly admissible rings is local
when it is stable under étale weak-ideal completion squares, descends along
those squares when `A → A'` is faithfully flat, and is stable under finite
products of targets.
-/

@[expose] public section

universe u

namespace TopologicalRing

/-- Finite products of weakly admissible rings are weakly admissible. -/
instance instIsWeaklyAdmissibleRingPi {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsWeaklyAdmissibleRing (A i)] :
    IsWeaklyAdmissibleRing (∀ i, A i) := sorry

/-- Finite products of countably indexed rings are countably indexed. -/
instance instIsCountablyIndexedPi {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsCountablyIndexed (A i)] :
    IsCountablyIndexed (∀ i, A i) := sorry

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)

/-- A property of morphisms of countably indexed weakly admissible rings is local
if it is stable under étale weak-ideal completion squares, descends along those
squares when `A → A'` is faithfully flat, and is stable under finite products of
targets. -/
structure IsLocalMorphismProperty : Prop where
  /-- For any localization square, `P φ` implies `P φ'`. -/
  localizeSquare :
    ∀ {A B A' B' : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
      [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
      (sq : LocalizeSquare A B A' B'),
      P sq.φ → P sq.φ'
  /-- For any localization square with `A → A'` faithfully flat, `P φ'` implies `P φ`. -/
  faithfullyFlat :
    ∀ {A B A' B' : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
      [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
      (sq : LocalizeSquare A B A' B'),
      (algebraMap A A').FaithfullyFlat → P sq.φ' → P sq.φ
  /-- If `P` holds for each `B →+* A i`, then it holds for `B →+* ∀ i, A i`. -/
  pi : ∀ {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
      [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
      [∀ i, IsWeaklyAdmissibleRing (A i)] [∀ i, IsCountablyIndexed (A i)]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
      (φ : ∀ i, B →+* A i),
      (∀ i, Continuous (φ i)) → (∀ i, P (φ i)) → P (RingHom.pi φ)

namespace IsLocalMorphismProperty

/-- Package the three locality axioms into a local morphism property. -/
def of
    (localizeSquare :
      ∀ {A B A' B' : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
        [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
        (sq : LocalizeSquare A B A' B'),
        P sq.φ → P sq.φ')
    (faithfullyFlat :
      ∀ {A B A' B' : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
        [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
        (sq : LocalizeSquare A B A' B'),
        (algebraMap A A').FaithfullyFlat → P sq.φ' → P sq.φ)
    (pi : ∀ {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
        [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
        [∀ i, IsWeaklyAdmissibleRing (A i)] [∀ i, IsCountablyIndexed (A i)]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : ∀ i, B →+* A i),
        (∀ i, Continuous (φ i)) → (∀ i, P (φ i)) → P (RingHom.pi φ)) :
    IsLocalMorphismProperty P where
  localizeSquare := localizeSquare
  faithfullyFlat := faithfullyFlat
  pi := pi

/-- A morphism property of `WAdm^count` is local iff it satisfies the three
étale-completion and finite-product axioms. -/
theorem iff :
    IsLocalMorphismProperty P ↔
      (∀ {A B A' B' : Type u}
          [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
          [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
          [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
          [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
          (sq : LocalizeSquare A B A' B'),
          P sq.φ → P sq.φ') ∧
        (∀ {A B A' B' : Type u}
            [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
            [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
            [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
            [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
            (sq : LocalizeSquare A B A' B'),
            (algebraMap A A').FaithfullyFlat → P sq.φ' → P sq.φ) ∧
          ∀ {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
            [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
            [∀ i, IsWeaklyAdmissibleRing (A i)] [∀ i, IsCountablyIndexed (A i)]
            [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
            (φ : ∀ i, B →+* A i),
            (∀ i, Continuous (φ i)) → (∀ i, P (φ i)) → P (RingHom.pi φ) := sorry

variable {P}

section LocalizeSquare

variable {A B A' B' : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
variable [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
variable [CommRing B'] [Algebra B B'] [Algebra.Etale B B']

/-- Local morphism properties are stable under étale weak-ideal completion squares. -/
theorem ofLocalizeSquare (hP : IsLocalMorphismProperty P)
    (sq : LocalizeSquare A B A' B') (hφ : P sq.φ) : P sq.φ' := sorry

/-- Local morphism properties descend along localization squares with faithfully
flat `A → A'`. -/
theorem ofFaithfullyFlat (hP : IsLocalMorphismProperty P)
    (sq : LocalizeSquare A B A' B') (hff : (algebraMap A A').FaithfullyFlat)
    (hφ' : P sq.φ') : P sq.φ := sorry

end LocalizeSquare

variable {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
variable [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
variable [∀ i, IsWeaklyAdmissibleRing (A i)] [∀ i, IsCountablyIndexed (A i)]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]

/-- Local morphism properties are stable under finite products of targets. -/
theorem ofPi (hP : IsLocalMorphismProperty P) (φ : ∀ i, B →+* A i)
    (hcont : ∀ i, Continuous (φ i)) (hφ : ∀ i, P (φ i)) : P (RingHom.pi φ) := sorry

end IsLocalMorphismProperty

end TopologicalRing
