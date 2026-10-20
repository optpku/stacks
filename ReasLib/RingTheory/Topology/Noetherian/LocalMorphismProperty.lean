/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.RingTheory.Topology.Noetherian
public import ReasLib.RingTheory.Topology.FiniteProducts
public import ReasLib.RingTheory.Topology.LocalizeSquare

/-!
# Local properties of morphisms of Noetherian adic rings

Local properties ascend along étale completion squares, descend along such
squares with faithfully flat source base change, and pass to finite products.
-/

@[expose] public section

universe u

namespace TopologicalRing.Noetherian

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)

/-- A property of morphisms of Noetherian adic rings is local if it is stable
under étale weak-ideal completion squares, descends along those squares when
`A → A'` is faithfully flat, and is stable under finite products of targets. -/
structure IsLocalMorphismProperty : Prop where
  /-- For any localization square in `WAdm^Noeth`, `P φ` implies `P φ'`. -/
  localizeSquare :
    ∀ {A B A' B' : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
      [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] [IsNoetherianRing A']
      [CommRing B'] [Algebra B B'] [Algebra.Etale B B'] [IsNoetherianRing B']
      (sq : LocalizeSquare A B A' B'),
      P sq.φ → P sq.φ'
  /-- For any localization square in `WAdm^Noeth` with `A → A'` faithfully
  flat, `P φ'` implies `P φ`. -/
  faithfullyFlat :
    ∀ {A B A' B' : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
      [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] [IsNoetherianRing A']
      [CommRing B'] [Algebra B B'] [Algebra.Etale B B'] [IsNoetherianRing B']
      (sq : LocalizeSquare A B A' B'),
      (algebraMap A A').FaithfullyFlat → P sq.φ' → P sq.φ
  /-- If `P` holds for each `B →+* A i`, then it holds for `B →+* ∀ i, A i`. -/
  pi : ∀ {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
      [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
      [∀ i, IsAdicRing (A i)] [∀ i, IsNoetherianRing (A i)]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
      (φ : ∀ i, B →+* A i),
      (∀ i, Continuous (φ i)) → (∀ i, P (φ i)) → P (RingHom.pi φ)

namespace IsLocalMorphismProperty

/-- Package the three locality axioms into a local morphism property of
Noetherian adic rings. -/
def of
    (localizeSquare :
      ∀ {A B A' B' : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] [IsNoetherianRing A']
        [CommRing B'] [Algebra B B'] [Algebra.Etale B B'] [IsNoetherianRing B']
        (sq : LocalizeSquare A B A' B'),
        P sq.φ → P sq.φ')
    (faithfullyFlat :
      ∀ {A B A' B' : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] [IsNoetherianRing A']
        [CommRing B'] [Algebra B B'] [Algebra.Etale B B'] [IsNoetherianRing B']
        (sq : LocalizeSquare A B A' B'),
        (algebraMap A A').FaithfullyFlat → P sq.φ' → P sq.φ)
    (pi : ∀ {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
        [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
        [∀ i, IsAdicRing (A i)] [∀ i, IsNoetherianRing (A i)]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : ∀ i, B →+* A i),
        (∀ i, Continuous (φ i)) → (∀ i, P (φ i)) → P (RingHom.pi φ)) :
    IsLocalMorphismProperty P where
  localizeSquare := localizeSquare
  faithfullyFlat := faithfullyFlat
  pi := pi

/-- A morphism property of `WAdm^Noeth` is local iff it satisfies the three
étale-completion and finite-product axioms. -/
theorem iff :
    IsLocalMorphismProperty P ↔
      (∀ {A B A' B' : Type u}
          [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
          [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
          [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] [IsNoetherianRing A']
          [CommRing B'] [Algebra B B'] [Algebra.Etale B B'] [IsNoetherianRing B']
          (sq : LocalizeSquare A B A' B'),
          P sq.φ → P sq.φ') ∧
        (∀ {A B A' B' : Type u}
            [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
            [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
            [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] [IsNoetherianRing A']
            [CommRing B'] [Algebra B B'] [Algebra.Etale B B'] [IsNoetherianRing B']
            (sq : LocalizeSquare A B A' B'),
            (algebraMap A A').FaithfullyFlat → P sq.φ' → P sq.φ) ∧
          ∀ {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
            [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
            [∀ i, IsAdicRing (A i)] [∀ i, IsNoetherianRing (A i)]
            [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
            (φ : ∀ i, B →+* A i),
            (∀ i, Continuous (φ i)) → (∀ i, P (φ i)) → P (RingHom.pi φ) := sorry

variable {P}

section LocalizeSquare

variable {A B A' B' : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
variable [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] [IsNoetherianRing A']
variable [CommRing B'] [Algebra B B'] [Algebra.Etale B B'] [IsNoetherianRing B']

/-- Local morphism properties of `WAdm^Noeth` are stable under étale weak-ideal
completion squares. -/
theorem ofLocalizeSquare (hP : IsLocalMorphismProperty P)
    (sq : LocalizeSquare A B A' B') (hφ : P sq.φ) : P sq.φ' := sorry

/-- Local morphism properties of `WAdm^Noeth` descend along localization squares
with faithfully flat `A → A'`. -/
theorem ofFaithfullyFlat (hP : IsLocalMorphismProperty P)
    (sq : LocalizeSquare A B A' B') (hff : (algebraMap A A').FaithfullyFlat)
    (hφ' : P sq.φ') : P sq.φ := sorry

end LocalizeSquare

variable {ι : Type u} [Finite ι] {A : ι → Type u} {B : Type u}
variable [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
variable [∀ i, IsAdicRing (A i)] [∀ i, IsNoetherianRing (A i)]
variable [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]

/-- Local morphism properties of `WAdm^Noeth` are stable under finite products
of targets. -/
theorem ofPi (hP : IsLocalMorphismProperty P) (φ : ∀ i, B →+* A i)
    (hcont : ∀ i, Continuous (φ i)) (hφ : ∀ i, P (φ i)) : P (RingHom.pi φ) := sorry

end IsLocalMorphismProperty

end TopologicalRing.Noetherian
