module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v w

namespace Ring.DirectLimit

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (φ : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (φ · · ·)]

/-- A compatible family of ring homomorphisms from a directed system of commutative rings
to a commutative ring factors uniquely through the canonical maps into its direct limit. -/
theorem existsUnique_hom {B : Type w} [CommRing B] (ψ : ∀ i, A i →+* B)
    (hψ : ∀ ⦃i j⦄ (hij : i ≤ j), (ψ j).comp (φ i j hij) = ψ i) :
    ∃! Ψ : Ring.DirectLimit A (φ · · ·) →+* B,
      ∀ i, ψ i = Ψ.comp (of A (φ · · ·) i) := sorry

end Ring.DirectLimit
