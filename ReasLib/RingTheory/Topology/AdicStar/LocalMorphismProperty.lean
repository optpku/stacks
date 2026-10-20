module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.RingTheory.Topology.AdicStar
public import ReasLib.RingTheory.Topology.LocalizeSquare

/-!
# Local properties of morphisms of adic* rings

A property of morphisms of `WAdm^{adic*}` is local when it is stable under
étale weak-ideal completion squares, descends along those squares when
`A → A'` is faithfully flat, and is stable under finite products of targets.
-/

@[expose] public section

universe u

namespace TopologicalRing.IsAdicStarRing

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)

/-- A property of morphisms of `WAdm^{adic*}` is local if it is stable under
étale weak-ideal completion squares, descends along those squares when
`A → A'` is faithfully flat, and is stable under finite products of targets. -/
structure IsLocalMorphismProperty : Prop where
  /-- For any localization square, `P φ` implies `P φ'`. -/
  localizeSquare :
    ∀ {A B A' B' : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
      [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
      (sq : LocalizeSquare A B A' B'),
      P sq.φ → P sq.φ'
  /-- For any localization square with `A → A'` faithfully flat, `P φ'` implies `P φ`. -/
  faithfullyFlat :
    ∀ {A B A' B' : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
      [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
      (sq : LocalizeSquare A B A' B'),
      (algebraMap A A').FaithfullyFlat → P sq.φ' → P sq.φ
  /-- If `P` holds for each `B →+* A i`, then it holds for `B →+* ∀ i, A i`. -/
  pi : ∀ {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
      [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
      [∀ i, IsAdicStarRing (A i)]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
      (φ : ∀ i, B →+* A i),
      (∀ i, Continuous (φ i)) → (∀ i, P (φ i)) → P (RingHom.pi φ)

namespace IsLocalMorphismProperty

/-- Étale-completion ascent, faithfully flat descent, and finite-product stability
define a local property of continuous homomorphisms of adic-star rings. -/
def of
    (localizeSquare :
      ∀ {A B A' B' : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
        [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
        (sq : LocalizeSquare A B A' B'),
        P sq.φ → P sq.φ')
    (faithfullyFlat :
      ∀ {A B A' B' : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
        [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
        (sq : LocalizeSquare A B A' B'),
        (algebraMap A A').FaithfullyFlat → P sq.φ' → P sq.φ)
    (pi : ∀ {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
        [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
        [∀ i, IsAdicStarRing (A i)]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        (φ : ∀ i, B →+* A i),
        (∀ i, Continuous (φ i)) → (∀ i, P (φ i)) → P (RingHom.pi φ)) :
    IsLocalMorphismProperty P where
  localizeSquare := localizeSquare
  faithfullyFlat := faithfullyFlat
  pi := pi

/-- A morphism property of `WAdm^{adic*}` is local iff it satisfies the three
étale-completion and finite-product axioms. -/
theorem iff :
    IsLocalMorphismProperty P ↔
      (∀ {A B A' B' : Type u}
          [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
          [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
          [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
          [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
          (sq : LocalizeSquare A B A' B'),
          P sq.φ → P sq.φ') ∧
        (∀ {A B A' B' : Type u}
            [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
            [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
            [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
            [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
            (sq : LocalizeSquare A B A' B'),
            (algebraMap A A').FaithfullyFlat → P sq.φ' → P sq.φ) ∧
          ∀ {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
            [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
            [∀ i, IsAdicStarRing (A i)]
            [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
            (φ : ∀ i, B →+* A i),
            (∀ i, Continuous (φ i)) → (∀ i, P (φ i)) → P (RingHom.pi φ) := sorry

/-- A local morphism property of `WAdm^{adic*}` unpacks as stability under
étale weak-ideal completion squares, descent along faithfully flat such
squares, and stability under finite products of targets. -/
theorem spec (hP : IsLocalMorphismProperty P) :
    (∀ {A B A' B' : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
        [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
        (sq : LocalizeSquare A B A' B'),
        P sq.φ → P sq.φ') ∧
      (∀ {A B A' B' : Type u}
          [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
          [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
          [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
          [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
          (sq : LocalizeSquare A B A' B'),
          (algebraMap A A').FaithfullyFlat → P sq.φ' → P sq.φ) ∧
        ∀ {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
          [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
          [∀ i, IsAdicStarRing (A i)]
          [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
          (φ : ∀ i, B →+* A i),
          (∀ i, Continuous (φ i)) → (∀ i, P (φ i)) → P (RingHom.pi φ) := sorry

variable {P}

section LocalizeSquare

variable {A B A' B' : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
variable [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
variable [CommRing B'] [Algebra B B'] [Algebra.Etale B B']

/-- Local morphism properties of `WAdm^{adic*}` are stable under étale
weak-ideal completion squares. -/
theorem ofLocalizeSquare (hP : IsLocalMorphismProperty P)
    (sq : LocalizeSquare A B A' B') (hφ : P sq.φ) : P sq.φ' := sorry

/-- Local morphism properties of `WAdm^{adic*}` descend along localization
squares with faithfully flat `A → A'`. -/
theorem ofFaithfullyFlat (hP : IsLocalMorphismProperty P)
    (sq : LocalizeSquare A B A' B') (hff : (algebraMap A A').FaithfullyFlat)
    (hφ' : P sq.φ') : P sq.φ := sorry

end LocalizeSquare

variable {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
variable [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
variable [∀ i, IsAdicStarRing (A i)]
variable [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]

/-- Local morphism properties of `WAdm^{adic*}` are stable under finite
products of targets. -/
theorem ofPi (hP : IsLocalMorphismProperty P) (φ : ∀ i, B →+* A i)
    (hcont : ∀ i, Continuous (φ i)) (hφ : ∀ i, P (φ i)) : P (RingHom.pi φ) :=
  sorry

end IsLocalMorphismProperty

end TopologicalRing.IsAdicStarRing
