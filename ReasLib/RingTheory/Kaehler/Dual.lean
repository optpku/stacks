/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dual derivations for independent Kähler differentials

@stack 07P2

This leaf records the reusable linear-algebra interface behind dual derivations. The construction
of a dual derivation uses a field-valued algebra, while the converse independence criterion works
for an arbitrary commutative algebra. p-basis arguments are supplied by the sibling
`FieldTheory.PBasis` leaves.
-/

@[expose] public section

universe u v w

namespace KaehlerDifferential

variable {R : Type u} {S : Type v}
variable {ι : Type w}

section Field

variable [CommRing R] [Field S] [Algebra R S]

/-- A linearly independent family of universal differentials admits a derivation dual to any one
of its prescribed elements. -/
@[stacks 07P2 "dual derivation for an independent differential family"]
theorem exists_dual_derivation (x : ι → S)
    (hx : LinearIndependent S (D R S ∘ x)) (i : ι) :
    ∃ θ : Derivation R S S,
      θ (x i) = 1 ∧ ∀ j, j ≠ i → θ (x j) = 0 := by
  classical
  let hli : LinearIndepOn S id (Set.range (D R S ∘ x)) := hx.linearIndepOn_id
  let b := Module.Basis.extend hli
  let bi : hli.extend (Set.subset_univ _) :=
    ⟨D R S (x i), hli.subset_extend _ ⟨i, rfl⟩⟩
  refine ⟨(b.coord bi).compDer (D R S), ?_, ?_⟩
  · change b.coord bi (D R S (x i)) = 1
    have hbi : b bi = (bi : Ω[S⁄R]) := Module.Basis.extend_apply_self hli bi
    change b.coord bi (bi : Ω[S⁄R]) = 1
    rw [← hbi]
    simp
  · intro j hji
    let bj : hli.extend (Set.subset_univ _) :=
      ⟨D R S (x j), hli.subset_extend _ ⟨j, rfl⟩⟩
    change b.coord bi (D R S (x j)) = 0
    have hbj : b bj = (bj : Ω[S⁄R]) := Module.Basis.extend_apply_self hli bj
    change b.coord bi (bj : Ω[S⁄R]) = 0
    have hbjne : bj ≠ bi := by
      intro h
      apply hji
      apply hx.injective
      exact congr_arg Subtype.val h
    rw [← hbj]
    simp [Module.Basis.coord, hbjne]

end Field

section CommRing

variable [CommRing R] [CommRing S] [Algebra R S]

/-- A family whose elements are separated by dual derivations has linearly independent universal
differentials. -/
@[stacks 07P2 "dual derivations imply differential independence"]
theorem linearIndependent_of_dual_derivations (x : ι → S)
    (hdual : ∀ i, ∃ θ : Derivation R S S,
      θ (x i) = 1 ∧ ∀ j, j ≠ i → θ (x j) = 0) :
    LinearIndependent S (D R S ∘ x) := by
  choose θ hθone hθzero using hdual
  apply LinearIndependent.of_pairwise_dual_eq_zero_one
    (D R S ∘ x) (fun i ↦ (θ i).liftKaehlerDifferential)
  · intro i j hij
    simp only [Function.comp_apply, Derivation.liftKaehlerDifferential_comp_D]
    exact hθzero i j hij.symm
  · intro i
    simpa only [Function.comp_apply, Derivation.liftKaehlerDifferential_comp_D] using hθone i

end CommRing

section FieldEquivalence

variable [CommRing R] [Field S] [Algebra R S]

/-- Linear independence of universal differentials is equivalent to the existence of derivations
dual to every member of the underlying family. -/
@[stacks 07P2 "differential independence via dual derivations"]
theorem linearIndependent_iff_dual_derivations (x : ι → S) :
    LinearIndependent S (D R S ∘ x) ↔
      ∀ i, ∃ θ : Derivation R S S,
        θ (x i) = 1 ∧ ∀ j, j ≠ i → θ (x j) = 0 := by
  constructor
  · intro hx i
    exact exists_dual_derivation x hx i
  · exact linearIndependent_of_dual_derivations x

end FieldEquivalence

end KaehlerDifferential
