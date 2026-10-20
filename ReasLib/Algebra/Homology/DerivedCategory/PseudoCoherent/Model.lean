module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Models of pseudo-coherent derived objects

This leaf exposes the bounded-above finite-free representative already encoded by
`DerivedCategory.IsPseudoCoherent`, with the comparison packaged as an explicit isomorphism.
@stack 064Q
@stack 064Y
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {R : Type u} [Ring R]
variable {K : DerivedCategory (ModuleCat R)}

/-- Stacks `064Q`: a pseudo-coherent derived module object has a bounded-above termwise finite-free model with
an explicit comparison isomorphism. -/
@[stacks 064Q "bounded-above finite-free model"]
theorem exists_finiteFree_model (hK : K.IsPseudoCoherent) :
    ∃ (P : CochainComplex (ModuleCat R) ℤ)
      (e : DerivedCategory.Q.obj P ≅ K),
      CochainComplex.minus (ModuleCat R) P ∧ P.IsTermwiseFiniteFree := sorry
/- Proof strategy: unfold the canonical pseudo-coherent derived-object predicate and extract its
bounded-above finite-free representative, packaging the quasi-isomorphism as the displayed
`DerivedCategory.Q.obj P ≅ K`. -/

end CategoryTheory.DerivedCategory.IsPseudoCoherent

namespace CategoryTheory.CochainComplex.IsPseudoCoherent

variable {R : Type u} [Ring R]

/-- Lemma 15.65.9 (Stacks `064Y`): a bounded-above cochain complex whose terms are pseudo-coherent is
pseudo-coherent. -/
@[stacks 064Y "bounded-above termwise pseudo-coherence"]
theorem of_boundedAbove_of_termwise
    (K : CochainComplex (ModuleCat R) ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hterm : ∀ i : ℤ, (K.X i).IsPseudoCoherent) :
    K.IsPseudoCoherent := sorry
/- Proof strategy: truncate the bounded-above complex degree by degree and use the triangulated
closure of pseudo-coherent objects; each successive cone is a shift of the pseudo-coherent term
provided by `hterm`, and the bounded-above limit is the original complex. -/

end CategoryTheory.CochainComplex.IsPseudoCoherent
