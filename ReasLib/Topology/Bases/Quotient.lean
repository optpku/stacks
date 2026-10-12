/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Bases
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotient Realizations of Basis Families

Existence of a continuous map whose saturated basis images realize a prescribed
open family.
-/

@[expose] public section

universe u

open Set

namespace TopologicalSpace

/-- Lemma 5.5.6: a covering open family with the stated intersection formula is realized by
inverse-saturated open basis images of a continuous map. -/
@[stacks 0D5Q "continuous quotient realization of a basis family"]
theorem exists_continuousMap_with_openBasisImages
    {X : Type u} [TopologicalSpace X] (B : Set (Set X))
    (hopen : ∀ U ∈ B, IsOpen U) (hcover : sUnion B = univ)
    (hinter : ∀ ⦃U V : Set X⦄, U ∈ B → V ∈ B →
      U ∩ V = ⋃₀ {W : Set X | W ∈ B ∧ W ⊆ U ∩ V}) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (f : C(X, Y)),
      (∀ U ∈ B, IsOpen (f '' U)) ∧
      (∀ U ∈ B, f ⁻¹' (f '' U) = U) ∧
      IsTopologicalBasis (image (f : X → Y) '' B) := sorry

end TopologicalSpace
