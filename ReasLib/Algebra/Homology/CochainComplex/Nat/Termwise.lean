module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise

/-!
# Termwise properties under extension of nonnegative complexes

Extension by zero from `ℕ` to `ℤ` preserves termwise finite freeness.  The instance is global
because this extension and the zero objects outside the image are canonical.
@stack 064Q
-/

@[expose] public section

universe u v

namespace CochainComplex.Nat

variable {R : Type u} [Ring R]

/-- Extending a termwise finite-free nonnegative complex by zero remains termwise finite free. -/
@[stacks 064Q "termwise finite freeness under extension by zero"]
instance extend_isTermwiseFiniteFree
    (K : CochainComplex (ModuleCat.{v} R) ℕ)
    [CochainComplex.Nat.IsTermwiseFiniteFree K] :
    (K.extend ComplexShape.embeddingUpNat).IsTermwiseFiniteFree := sorry

end CochainComplex.Nat
